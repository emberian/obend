#![forbid(unsafe_code)]
//! "Epiphany Lens" trusted AR display scanout compositor, `obend-surfaces` `ViewNode`/`Frustum`
//! overlay validator/clipper, and monotone counter-bound CSI-2 sensor frame redactor & sealer
//! (`OBEND.SHE.SENSOR_SEAL/v1`).
//!
//! Security invariants enforced fail-closed:
//! 1. **Trusted Consent Chrome Non-Occlusion & Unforgeability**:
//!    - Untrusted belief-circle `ViewNode` trees are first scrubbed through
//!      `crate::project_view_node` (`Frustum` fog-of-war membrane), checked against hardware
//!      consent-chrome spoofing markers, and either refused (`IntrusionPolicy::Refuse`) or
//!      strictly clipped outside `TrustedConsentBand`.
//!    - At scanout time, any untrusted pixel falling inside `TrustedConsentBand` is hard-zeroed,
//!      and opaque (`a == 255`) `TrustedConsentChromePlane` pixels (`TrustedConsentBand` and
//!      active `ConsentModalRect`) dominate the Porter-Duff `over` Z-order (`UntrustedBeliefPlane`
//!      -> `PhysicalHazardReticlePlane` -> `TrustedConsentChromePlane`).
//! 2. **Physical Hazard Reticle Visibility Floor**:
//!    - Every active dual-tone `PhysicalHazardBox` (`hi_color` outer ring, `lo_color` inner ring)
//!      must satisfy both the minimum alpha floor (`a >= min_alpha`) and the worst-case BT.601
//!      post-composite luma contrast floor (`luma(over(hi, bg1)) >= luma(over(lo, bg2)) +
//!      min_contrast`) across all adversarial background pixels `bg1, bg2 in [0, 255]^4`.
//! 3. **Monotone Sensor Frame Sealing & Zero Private ROI Leakage (`OBEND.SHE.SENSOR_SEAL/v1`)**:
//!    - `SensorFrameSealer` enforces strictly monotone `(sensor_id, mono_seq)`, zeroes all pixels
//!      inside declared `redact_boxes` across all CSI-2 `SensorTile`s before untrusted consumers
//!      or the hash function see them, and binds all 6 post-redaction frame fields with a 256-bit
//!      NIST SP 800-185 `cSHAKE256` commitment matching `Obend.Polis.EpiphanyCompositor`
//!      byte-for-byte.

use std::collections::BTreeMap;

use crate::{
    project_view_node, Frustum, HostStatus, ViewNode, WorldState, MAX_VIEW_DEPTH, MAX_VIEW_NODES,
};

/// 256-bit cryptographic digest carrier (`cSHAKE256` 32-byte output).
pub type Digest = [u8; 32];

/// Canonical NIST SP 800-185 `cSHAKE256` customization domain for sealed sensor frames.
/// Matches `Obend.Polis.EpiphanyCompositor` (`OBEND.SHE.SENSOR_SEAL/v1`).
pub const SENSOR_SEAL_DOMAIN: &str = "OBEND.SHE.SENSOR_SEAL/v1";

/// Default minimum opacity (`~80%`) for active physical hazard reticles.
pub const DEFAULT_MIN_HAZARD_ALPHA: u8 = 204;

/// Default minimum worst-case BT.601 post-composite luma contrast guaranteed between the outer
/// (`hi_color`) and inner (`lo_color`) rings of any active `PhysicalHazardBox` over any
/// adversarial background pair.
pub const DEFAULT_MIN_HAZARD_CONTRAST: u8 = 128;

/// Reserved hardware-chrome tokens that untrusted belief-circle `ViewNode` surfaces are forbidden
/// from spoofing in titles, tags, labels, handles, turn names, or hosted cell names.
const RESERVED_CHROME_MARKERS: &[&str] = &[
    "she.consent",
    "obend.chrome",
    "trusted_consent",
    "consent_modal",
    "hardware_led",
    "sensor_led",
    "epiphany.chrome",
];

// ---------------------------------------------------------------------------
// Geometry, Color & Exact Integer [0, 255] Porter-Duff `over` Arithmetic
// ---------------------------------------------------------------------------

/// Discrete 2D display viewport dimensions in pixels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Viewport {
    pub width: u32,
    pub height: u32,
}

impl Viewport {
    pub const fn new(width: u32, height: u32) -> Self {
        Self { width, height }
    }

    pub const fn is_empty(self) -> bool {
        self.width == 0 || self.height == 0
    }

    pub const fn full_rect(self) -> Rect {
        Rect {
            x: 0,
            y: 0,
            width: self.width,
            height: self.height,
        }
    }

    pub fn pixel_count(self) -> Option<usize> {
        let w = usize::try_from(self.width).ok()?;
        let h = usize::try_from(self.height).ok()?;
        w.checked_mul(h)
    }

    pub fn contains(self, x: u32, y: u32) -> bool {
        x < self.width && y < self.height
    }

    pub fn pixel_index(self, x: u32, y: u32) -> Option<usize> {
        if !self.contains(x, y) {
            return None;
        }
        let row = usize::try_from(y).ok()?;
        let w = usize::try_from(self.width).ok()?;
        let col = usize::try_from(x).ok()?;
        row.checked_mul(w)?.checked_add(col)
    }
}

/// Axis-aligned half-open pixel rectangle `[x, x + width) x [y, y + height)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rect {
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
}

impl Rect {
    pub const fn new(x: u32, y: u32, width: u32, height: u32) -> Self {
        Self {
            x,
            y,
            width,
            height,
        }
    }

    pub const fn is_empty(self) -> bool {
        self.width == 0 || self.height == 0
    }

    pub const fn right_u64(self) -> u64 {
        self.x as u64 + self.width as u64
    }

    pub const fn bottom_u64(self) -> u64 {
        self.y as u64 + self.height as u64
    }

    pub fn x_end(self) -> Option<u32> {
        self.x.checked_add(self.width)
    }

    pub fn y_end(self) -> Option<u32> {
        self.y.checked_add(self.height)
    }

    pub fn fits_within(self, viewport: Viewport) -> bool {
        match (self.x_end(), self.y_end()) {
            (Some(xe), Some(ye)) => xe <= viewport.width && ye <= viewport.height,
            _ => false,
        }
    }

    pub fn contains(self, px: u32, py: u32) -> bool {
        if self.is_empty() {
            return false;
        }
        let px64 = px as u64;
        let py64 = py as u64;
        px64 >= self.x as u64
            && px64 < self.right_u64()
            && py64 >= self.y as u64
            && py64 < self.bottom_u64()
    }

    pub const fn intersects(self, other: Rect) -> bool {
        if self.is_empty() || other.is_empty() {
            return false;
        }
        (self.x as u64) < other.right_u64()
            && (other.x as u64) < self.right_u64()
            && (self.y as u64) < other.bottom_u64()
            && (other.y as u64) < self.bottom_u64()
    }

    pub fn intersection(self, other: Rect) -> Option<Rect> {
        if !self.intersects(other) {
            return None;
        }
        let x0 = self.x.max(other.x) as u64;
        let y0 = self.y.max(other.y) as u64;
        let x1 = self.right_u64().min(other.right_u64());
        let y1 = self.bottom_u64().min(other.bottom_u64());
        if x1 <= x0 || y1 <= y0 {
            return None;
        }
        Some(Rect {
            x: u32::try_from(x0).ok()?,
            y: u32::try_from(y0).ok()?,
            width: u32::try_from(x1 - x0).ok()?,
            height: u32::try_from(y1 - y0).ok()?,
        })
    }

    pub const fn area_u64(self) -> u64 {
        (self.width as u64) * (self.height as u64)
    }

    /// Clip `self` to `viewport` and subtract `excluded` so the returned rectangle (if any) is
    /// strictly non-empty, contained in `self` and `viewport`, and disjoint from `excluded`.
    pub fn clip_excluding(self, excluded: Rect, viewport: Viewport) -> Option<Rect> {
        let clamped = self.intersection(viewport.full_rect())?;
        if !clamped.intersects(excluded) {
            return Some(clamped);
        }
        let cx0 = clamped.x as u64;
        let cy0 = clamped.y as u64;
        let cx1 = clamped.right_u64();
        let cy1 = clamped.bottom_u64();

        let ex0 = excluded.x as u64;
        let ey0 = excluded.y as u64;
        let ex1 = excluded.right_u64();
        let ey1 = excluded.bottom_u64();

        let mut candidates = [None; 4];
        if ey1 < cy1 {
            let ny0 = ey1.max(cy0);
            if cy1 > ny0 {
                candidates[0] = Some(Rect::new(
                    cx0 as u32,
                    ny0 as u32,
                    (cx1 - cx0) as u32,
                    (cy1 - ny0) as u32,
                ));
            }
        }
        if ey0 > cy0 {
            let ny1 = ey0.min(cy1);
            if ny1 > cy0 {
                candidates[1] = Some(Rect::new(
                    cx0 as u32,
                    cy0 as u32,
                    (cx1 - cx0) as u32,
                    (ny1 - cy0) as u32,
                ));
            }
        }
        if ex1 < cx1 {
            let nx0 = ex1.max(cx0);
            if cx1 > nx0 {
                candidates[2] = Some(Rect::new(
                    nx0 as u32,
                    cy0 as u32,
                    (cx1 - nx0) as u32,
                    (cy1 - cy0) as u32,
                ));
            }
        }
        if ex0 > cx0 {
            let nx1 = ex0.min(cx1);
            if nx1 > cx0 {
                candidates[3] = Some(Rect::new(
                    cx0 as u32,
                    cy0 as u32,
                    (nx1 - cx0) as u32,
                    (cy1 - cy0) as u32,
                ));
            }
        }

        candidates
            .into_iter()
            .flatten()
            .filter(|r| !r.is_empty() && !r.intersects(excluded) && r.fits_within(viewport))
            .max_by_key(|r| r.area_u64())
    }

    /// Distance in pixels from `(px, py)` to the nearest edge of `self` (`None` if outside).
    pub fn edge_distance(self, px: u32, py: u32) -> Option<u32> {
        if !self.contains(px, py) {
            return None;
        }
        let dx_left = (px as u64) - (self.x as u64);
        let dx_right = (self.right_u64() - 1) - (px as u64);
        let dy_top = (py as u64) - (self.y as u64);
        let dy_bottom = (self.bottom_u64() - 1) - (py as u64);
        let min_d = dx_left.min(dx_right).min(dy_top).min(dy_bottom);
        u32::try_from(min_d).ok()
    }
}

/// 8-bit per channel RGBA pixel in `[0, 255]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Rgba {
    pub r: u8,
    pub g: u8,
    pub b: u8,
    pub a: u8,
}

impl Rgba {
    pub const TRANSPARENT: Self = Self::new(0, 0, 0, 0);
    pub const BLACK: Self = Self::new(0, 0, 0, 255);
    pub const WHITE: Self = Self::new(255, 255, 255, 255);
    /// High-luminance outer reticle ring (`luma(over(hi, BLACK)) = 203` at `a = 230`).
    pub const HAZARD_HI_YELLOW: Self = Self::new(255, 255, 0, 230);
    /// High-luminance outer white reticle ring (`luma(over(hi, BLACK)) = 229` at `a = 230`).
    pub const HAZARD_HI_WHITE: Self = Self::new(255, 255, 255, 230);
    /// Low-luminance inner reticle ring (`luma(over(lo, WHITE)) = 25` at `a = 230`).
    pub const HAZARD_LO_BLACK: Self = Self::new(0, 0, 0, 230);
    pub const CHROME_SLATE: Self = Self::new(18, 24, 38, 255);
    pub const SENSOR_LED_GREEN: Self = Self::new(0, 230, 118, 255);

    pub const fn new(r: u8, g: u8, b: u8, a: u8) -> Self {
        Self { r, g, b, a }
    }

    pub const fn to_bytes(self) -> [u8; 4] {
        [self.r, self.g, self.b, self.a]
    }

    pub const fn from_bytes(b: [u8; 4]) -> Self {
        Self {
            r: b[0],
            g: b[1],
            b: b[2],
            a: b[3],
        }
    }
}

/// Exact integer BT.601 luma matching `Obend.Polis.EpiphanyCompositor`:
/// `luma(r, g, b) = (77 * r + 150 * g + 29 * b) / 256`.
pub const fn luma_bt601(px: Rgba) -> u8 {
    ((77 * px.r as u32 + 150 * px.g as u32 + 29 * px.b as u32) / 256) as u8
}

/// Exact integer `[0, 255]` Porter-Duff channel blend:
/// `floor((src * src_alpha + dst * (255 - src_alpha)) / 255)`.
pub const fn blend_channel(src: u8, dst: u8, src_alpha: u8) -> u8 {
    let s = src as u32;
    let d = dst as u32;
    let a = src_alpha as u32;
    ((s * a + d * (255 - a)) / 255) as u8
}

/// Exact integer `[0, 255]` Porter-Duff alpha blend:
/// `src_alpha + floor(dst_alpha * (255 - src_alpha) / 255)`.
pub const fn blend_alpha(src_alpha: u8, dst_alpha: u8) -> u8 {
    let sa = src_alpha as u32;
    let da = dst_alpha as u32;
    (sa + (da * (255 - sa)) / 255) as u8
}

/// Exact integer `[0, 255]` Porter-Duff `src over dst`.
/// - When `src.a == 255`, returns `src` identically regardless of `dst`.
/// - When `src.a == 0`, returns `dst` identically.
pub const fn porter_duff_over(src: Rgba, dst: Rgba) -> Rgba {
    Rgba {
        r: blend_channel(src.r, dst.r, src.a),
        g: blend_channel(src.g, dst.g, src.a),
        b: blend_channel(src.b, dst.b, src.a),
        a: blend_alpha(src.a, dst.a),
    }
}

/// Guaranteed worst-case post-composite BT.601 luma contrast between `hi_color` (outer ring)
/// and `lo_color` (inner ring) across ALL adversarial background pairs `(bg1, bg2)`:
/// `luma_bt601(over(hi_color, BLACK)).saturating_sub(luma_bt601(over(lo_color, WHITE)))`.
pub const fn worst_case_dual_tone_contrast(hi_color: Rgba, lo_color: Rgba) -> u8 {
    let min_hi = luma_bt601(porter_duff_over(hi_color, Rgba::BLACK));
    let max_lo = luma_bt601(porter_duff_over(lo_color, Rgba::WHITE));
    min_hi.saturating_sub(max_lo)
}

// ---------------------------------------------------------------------------
// Fail-Closed Refusal Diagnostics
// ---------------------------------------------------------------------------

/// Structured fail-closed refusal reasons for the Epiphany scanout compositor and sensor sealer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EpiphanyRefusal {
    /// An untrusted belief-circle `ViewNode` overlay attempted to paint inside `TrustedConsentBand`.
    ChromeBandIntrusion {
        circle_id: String,
        attempted: Rect,
        reserved_band: Rect,
    },
    /// An untrusted belief-circle `ViewNode` attempted to spoof reserved hardware consent chrome.
    ChromeSpoofAttempt { circle_id: String, reason: String },
    /// An active `PhysicalHazardBox` failed the guaranteed alpha or dual-tone luma contrast floor.
    HazardVisibilityViolation {
        hazard_id: String,
        actual_min_alpha: u8,
        min_alpha: u8,
        actual_contrast: u8,
        min_contrast: u8,
    },
    /// A sensor frame attempted replay or sequence rollback (`attempted_seq <= last_seq`).
    SensorSeqRollback {
        sensor_id: u64,
        last_seq: u64,
        attempted_seq: u64,
    },
    /// A sensor frame attempted to use `u64::MAX`, risking monotone counter overflow/wraparound.
    SensorSeqOverflow { sensor_id: u64, attempted_seq: u64 },
    /// A streaming scanline packet violated geometry, duplicate-line, or full-frame coverage rules.
    ScanlineStreamViolation { reason: &'static str },
    /// A sealed sensor frame's 256-bit `OBEND.SHE.SENSOR_SEAL/v1` digest did not match.
    SealDigestMismatch { expected: Digest, actual: Digest },
    /// A purportedly redacted sensor frame still contained non-zero pixels inside a `redact_box`.
    UnredactedPrivateRoi {
        tile_index: usize,
        box_index: usize,
        x: u32,
        y: u32,
    },
    /// Invalid viewport, rectangle, tile geometry, buffer size, or non-opaque chrome config.
    InvalidGeometry { reason: &'static str },
    /// Untrusted `ViewNode` exceeded `MAX_VIEW_DEPTH` or `MAX_VIEW_NODES`.
    ViewBudgetExceeded { reason: &'static str },
}

// ---------------------------------------------------------------------------
// Plane 3: Trusted Consent Chrome Plane (`TrustedConsentBand` + `ConsentModalRect`)
// ---------------------------------------------------------------------------

/// Hardware-reserved non-occludable top/border band for capability & active-sensor indicators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TrustedConsentBand {
    pub rect: Rect,
}

impl TrustedConsentBand {
    pub const fn top_bar(viewport: Viewport, band_height: u32) -> Self {
        Self {
            rect: Rect::new(0, 0, viewport.width, band_height),
        }
    }
}

/// Hardware-attested capability/quorum consent modal overlay (strictly opaque `a == 255`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsentModalRect {
    pub rect: Rect,
    pub prompt: String,
    pub quorum_epoch: u64,
    pub bg: Rgba,
    pub border_accent: Rgba,
}

impl ConsentModalRect {
    pub fn validate(&self, viewport: Viewport) -> Result<(), EpiphanyRefusal> {
        if self.rect.is_empty() || !self.rect.fits_within(viewport) {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "consent modal rect must be non-empty and within viewport",
            });
        }
        if self.bg.a != 255 || self.border_accent.a != 255 {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "consent modal chrome colors must be strictly opaque (a == 255)",
            });
        }
        Ok(())
    }

    pub fn pixel_at(&self, x: u32, y: u32) -> Option<Rgba> {
        let dist = self.rect.edge_distance(x, y)?;
        if dist == 0 {
            Some(self.border_accent)
        } else {
            Some(self.bg)
        }
    }
}

/// Highest-priority hardware-attested scanout plane (`TrustedConsentBand` + active-sensor LED
/// indicator + optional `ConsentModalRect`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustedConsentChromePlane {
    pub viewport: Viewport,
    pub consent_band: TrustedConsentBand,
    pub modal: Option<ConsentModalRect>,
    pub sensor_led_active: bool,
    pub band_bg: Rgba,
    pub led_color: Rgba,
}

impl TrustedConsentChromePlane {
    pub fn validate(&self) -> Result<(), EpiphanyRefusal> {
        if self.viewport.is_empty() {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "chrome viewport must be non-empty",
            });
        }
        if self.consent_band.rect.is_empty() || !self.consent_band.rect.fits_within(self.viewport) {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "trusted consent band must be non-empty and within viewport",
            });
        }
        if self.band_bg.a != 255 || self.led_color.a != 255 {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason:
                    "trusted consent band and sensor LED colors must be strictly opaque (a == 255)",
            });
        }
        if let Some(modal) = &self.modal {
            modal.validate(self.viewport)?;
        }
        Ok(())
    }

    /// Deterministic LED indicator sub-rectangle tucked inside the right end of `consent_band`.
    pub fn sensor_led_rect(&self) -> Rect {
        let b = self.consent_band.rect;
        let size = b.height.min(b.width).clamp(1, 4);
        let x = b.x + b.width.saturating_sub(size);
        Rect::new(x, b.y, size, size)
    }

    /// Returns true if `(x, y)` lies inside hardware-protected consent chrome.
    pub fn is_protected_pixel(&self, x: u32, y: u32) -> bool {
        self.consent_band.rect.contains(x, y)
            || self.modal.as_ref().is_some_and(|m| m.rect.contains(x, y))
    }

    /// Hardware-attested chrome pixel at `(x, y)` (`a == 255` on every protected pixel,
    /// `Rgba::TRANSPARENT` outside).
    pub fn pixel_at(&self, x: u32, y: u32) -> Rgba {
        if self.consent_band.rect.contains(x, y) {
            if self.sensor_led_active && self.sensor_led_rect().contains(x, y) {
                return self.led_color;
            }
            return self.band_bg;
        }
        if let Some(modal) = &self.modal {
            if let Some(px) = modal.pixel_at(x, y) {
                return px;
            }
        }
        Rgba::TRANSPARENT
    }
}

// ---------------------------------------------------------------------------
// Plane 2: Physical Hazard Reticle Plane (Dual-Tone Outer/Inner Ring)
// ---------------------------------------------------------------------------

/// Which ring of a dual-tone `PhysicalHazardBox` covers a pixel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HazardRing {
    OuterHi,
    InnerLo,
}

/// A kinematic/physical obstacle hazard reticle rendered above untrusted belief overlays.
/// Uses a dual-tone ring (`hi_color` outer ring at `[0, stroke_width)`, `lo_color` inner ring
/// at `[stroke_width, 2 * stroke_width)`) to guarantee BT.601 luma contrast against arbitrary
/// adversarial backgrounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalHazardBox {
    pub hazard_id: String,
    pub rect: Rect,
    /// Thickness of each ring in pixels (must be `>= 1` so both outer and inner rings render).
    pub stroke_width: u32,
    pub hi_color: Rgba,
    pub lo_color: Rgba,
    /// Higher severity wins when two hazard boxes overlap at the same pixel.
    pub severity: u8,
}

impl PhysicalHazardBox {
    pub fn ring_at(&self, x: u32, y: u32) -> Option<HazardRing> {
        if self.stroke_width == 0 {
            return None;
        }
        let dist = self.rect.edge_distance(x, y)?;
        let sw = self.stroke_width;
        if dist < sw {
            Some(HazardRing::OuterHi)
        } else if dist < sw.saturating_mul(2) {
            Some(HazardRing::InnerLo)
        } else {
            None
        }
    }

    pub fn pixel_at(&self, x: u32, y: u32) -> Option<Rgba> {
        match self.ring_at(x, y)? {
            HazardRing::OuterHi => Some(self.hi_color),
            HazardRing::InnerLo => Some(self.lo_color),
        }
    }

    pub fn covers_pixel(&self, x: u32, y: u32) -> bool {
        self.ring_at(x, y).is_some()
    }
}

/// Middle scanout plane enforcing guaranteed alpha and dual-tone BT.601 luma contrast floors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalHazardReticlePlane {
    pub viewport: Viewport,
    pub min_alpha: u8,
    pub min_contrast: u8,
    pub boxes: Vec<PhysicalHazardBox>,
}

impl PhysicalHazardReticlePlane {
    pub fn new(viewport: Viewport, min_alpha: u8, min_contrast: u8) -> Self {
        Self {
            viewport,
            min_alpha,
            min_contrast,
            boxes: Vec::new(),
        }
    }

    pub fn validate(&self) -> Result<(), EpiphanyRefusal> {
        if self.viewport.is_empty() {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "hazard plane viewport must be non-empty",
            });
        }
        for h in &self.boxes {
            if h.rect.is_empty() || !h.rect.fits_within(self.viewport) {
                return Err(EpiphanyRefusal::InvalidGeometry {
                    reason: "physical hazard box must be non-empty and within viewport",
                });
            }
            let min_span = h.stroke_width.saturating_mul(4);
            if h.stroke_width == 0 || h.rect.width < min_span || h.rect.height < min_span {
                return Err(EpiphanyRefusal::InvalidGeometry {
                    reason: "physical hazard box must accommodate dual-tone outer and inner rings",
                });
            }
            let actual_min_alpha = h.hi_color.a.min(h.lo_color.a);
            let actual_contrast = worst_case_dual_tone_contrast(h.hi_color, h.lo_color);
            if actual_min_alpha < self.min_alpha || actual_contrast < self.min_contrast {
                return Err(EpiphanyRefusal::HazardVisibilityViolation {
                    hazard_id: h.hazard_id.clone(),
                    actual_min_alpha,
                    min_alpha: self.min_alpha,
                    actual_contrast,
                    min_contrast: self.min_contrast,
                });
            }
        }
        Ok(())
    }

    /// Returns the highest-severity active hazard pixel at `(x, y)` (or `Rgba::TRANSPARENT`).
    pub fn pixel_at(&self, x: u32, y: u32) -> Rgba {
        let mut best: Option<(u8, Rgba)> = None;
        for h in &self.boxes {
            if let Some(color) = h.pixel_at(x, y) {
                match best {
                    None => best = Some((h.severity, color)),
                    Some((sev, _)) if h.severity >= sev => best = Some((h.severity, color)),
                    _ => {}
                }
            }
        }
        best.map_or(Rgba::TRANSPARENT, |(_, c)| c)
    }

    pub fn has_active_hazard_at(&self, x: u32, y: u32) -> bool {
        self.boxes.iter().any(|h| h.covers_pixel(x, y))
    }
}

// ---------------------------------------------------------------------------
// Plane 1: Untrusted Belief-Circle `ViewNode` + `Frustum` Compiler & Plane
// ---------------------------------------------------------------------------

/// Policy applied when an untrusted belief-circle `ViewNode` requests a rect overlapping
/// `TrustedConsentBand`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntrusionPolicy {
    /// Fail closed with `EpiphanyRefusal::ChromeBandIntrusion`.
    Refuse,
    /// Deterministically clip the overlay strictly outside `TrustedConsentBand`.
    ClipToSafeRegion,
}

/// Untrusted belief-circle `ViewNode` overlay submission bound to an `obend-surfaces` cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BeliefOverlaySpec {
    pub circle_id: String,
    pub cell: String,
    pub requested_rect: Rect,
    pub root: ViewNode,
    pub fill_color: Rgba,
}

/// A single validated, viewport-bounded overlay primitive compiled from a `Frustum`-projected
/// `ViewNode` subtree. Always disjoint from `TrustedConsentBand`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledOverlayBox {
    pub circle_id: String,
    pub rect: Rect,
    pub node_tag: u8,
    pub color: Rgba,
}

/// Result of compiling an untrusted `BeliefOverlaySpec` through `Frustum` scrubbing, chrome-spoof
/// validation, and `TrustedConsentBand` clipping/refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledBeliefOverlay {
    pub circle_id: String,
    pub safe_rect: Option<Rect>,
    pub projected_tree: ViewNode,
    pub boxes: Vec<CompiledOverlayBox>,
}

fn contains_reserved_chrome_marker(s: &str) -> Option<&'static str> {
    let lower = s.to_ascii_lowercase();
    RESERVED_CHROME_MARKERS
        .iter()
        .copied()
        .find(|marker| lower.contains(marker))
}

fn check_str_no_spoof(circle_id: &str, field: &str, value: &str) -> Result<(), EpiphanyRefusal> {
    if let Some(marker) = contains_reserved_chrome_marker(value) {
        return Err(EpiphanyRefusal::ChromeSpoofAttempt {
            circle_id: circle_id.to_owned(),
            reason: format!("reserved hardware chrome marker `{marker}` in {field}"),
        });
    }
    Ok(())
}

fn validate_belief_tree(
    circle_id: &str,
    node: &ViewNode,
    depth: usize,
    node_count: &mut usize,
) -> Result<(), EpiphanyRefusal> {
    if depth > MAX_VIEW_DEPTH {
        return Err(EpiphanyRefusal::ViewBudgetExceeded {
            reason: "belief ViewNode exceeded MAX_VIEW_DEPTH",
        });
    }
    *node_count += 1;
    if *node_count > MAX_VIEW_NODES {
        return Err(EpiphanyRefusal::ViewBudgetExceeded {
            reason: "belief ViewNode exceeded MAX_VIEW_NODES",
        });
    }
    match node {
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                validate_belief_tree(circle_id, c, depth + 1, node_count)?;
            }
        }
        ViewNode::Text(s) => check_str_no_spoof(circle_id, "Text", s)?,
        ViewNode::Bind { label, .. } => check_str_no_spoof(circle_id, "Bind.label", label)?,
        ViewNode::Button { label, turn, .. } => {
            check_str_no_spoof(circle_id, "Button.label", label)?;
            check_str_no_spoof(circle_id, "Button.turn", turn)?;
        }
        ViewNode::Input {
            bind_view,
            fire_turn,
            submit_label,
        } => {
            check_str_no_spoof(circle_id, "Input.bind_view", bind_view)?;
            check_str_no_spoof(circle_id, "Input.fire_turn", fire_turn)?;
            check_str_no_spoof(circle_id, "Input.submit_label", submit_label)?;
        }
        ViewNode::Section {
            title,
            tag,
            children,
        } => {
            check_str_no_spoof(circle_id, "Section.title", title)?;
            check_str_no_spoof(circle_id, "Section.tag", tag)?;
            for c in children {
                validate_belief_tree(circle_id, c, depth + 1, node_count)?;
            }
        }
        ViewNode::Tabs {
            tabs,
            select_turn,
            panels,
            ..
        } => {
            for t in tabs {
                check_str_no_spoof(circle_id, "Tabs.tab", t)?;
            }
            check_str_no_spoof(circle_id, "Tabs.select_turn", select_turn)?;
            for p in panels {
                validate_belief_tree(circle_id, p, depth + 1, node_count)?;
            }
        }
        ViewNode::Gauge { label, .. } => check_str_no_spoof(circle_id, "Gauge.label", label)?,
        ViewNode::Divider => {}
        ViewNode::Host { cell, status, view } => {
            check_str_no_spoof(circle_id, "Host.cell", cell)?;
            if let HostStatus::Interposed { label } = status {
                check_str_no_spoof(circle_id, "Host.label", label)?;
            }
            if let Some(inner) = view {
                validate_belief_tree(circle_id, inner, depth + 1, node_count)?;
            }
        }
        ViewNode::Grid { children, .. } => {
            for c in children {
                validate_belief_tree(circle_id, c, depth + 1, node_count)?;
            }
        }
        ViewNode::Breadcrumb { items } => {
            for c in items {
                check_str_no_spoof(circle_id, "Breadcrumb.label", &c.label)?;
                check_str_no_spoof(circle_id, "Breadcrumb.turn", &c.turn)?;
            }
        }
        ViewNode::Progress { label, .. } => check_str_no_spoof(circle_id, "Progress.label", label)?,
        ViewNode::Pill {
            text, tag, cases, ..
        } => {
            check_str_no_spoof(circle_id, "Pill.text", text)?;
            check_str_no_spoof(circle_id, "Pill.tag", tag)?;
            for pc in cases {
                check_str_no_spoof(circle_id, "PillCase.label", &pc.label)?;
                check_str_no_spoof(circle_id, "PillCase.tag", &pc.tag)?;
            }
        }
        ViewNode::Icon { glyph, tag } => {
            check_str_no_spoof(circle_id, "Icon.glyph", glyph)?;
            check_str_no_spoof(circle_id, "Icon.tag", tag)?;
        }
        ViewNode::Menu { items } => {
            for it in items {
                check_str_no_spoof(circle_id, "MenuItem.label", &it.label)?;
                check_str_no_spoof(circle_id, "MenuItem.turn", &it.turn)?;
            }
        }
        ViewNode::Halo { handles, .. } => {
            for h in handles {
                check_str_no_spoof(circle_id, "HaloHandle.glyph", &h.glyph)?;
                check_str_no_spoof(circle_id, "HaloHandle.turn", &h.turn)?;
            }
        }
        ViewNode::Slider { turn, .. } => check_str_no_spoof(circle_id, "Slider.turn", turn)?,
        ViewNode::Toggle {
            on_turn,
            off_turn,
            label,
            ..
        } => {
            check_str_no_spoof(circle_id, "Toggle.on_turn", on_turn)?;
            check_str_no_spoof(circle_id, "Toggle.off_turn", off_turn)?;
            check_str_no_spoof(circle_id, "Toggle.label", label)?;
        }
        ViewNode::Tile { handle, .. } => check_str_no_spoof(circle_id, "Tile.handle", handle)?,
        ViewNode::CoordGrid { cells, .. } => {
            for cell in cells {
                check_str_no_spoof(circle_id, "CoordCell.tag", &cell.tag)?;
                check_str_no_spoof(circle_id, "CoordCell.turn", &cell.turn)?;
            }
        }
        ViewNode::Adept(inner) => validate_belief_tree(circle_id, inner, depth + 1, node_count)?,
    }
    Ok(())
}

fn modulate_color(base: Rgba, node: &ViewNode) -> Rgba {
    let tweak: u8 = match node {
        ViewNode::Bind {
            resolved: Some(v), ..
        }
        | ViewNode::Gauge {
            resolved: Some(v), ..
        }
        | ViewNode::Slider {
            resolved: Some(v), ..
        }
        | ViewNode::Toggle {
            resolved: Some(v), ..
        }
        | ViewNode::Pill {
            resolved: Some(v), ..
        } => (*v & 0x1f) as u8,
        ViewNode::Progress { value, .. } => (*value & 0x1f) as u8,
        _ => node.variant_tag(),
    };
    Rgba::new(
        base.r.saturating_add(tweak),
        base.g,
        base.b.saturating_sub(tweak / 2),
        base.a,
    )
}

fn layout_projected_boxes(
    circle_id: &str,
    node: &ViewNode,
    bounds: Rect,
    base_color: Rgba,
    out: &mut Vec<CompiledOverlayBox>,
) {
    if bounds.is_empty() {
        return;
    }
    match node {
        ViewNode::VStack(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            if cs.is_empty() {
                return;
            }
            let n = cs.len() as u32;
            let slice_h = bounds.height / n;
            if slice_h == 0 {
                out.push(CompiledOverlayBox {
                    circle_id: circle_id.to_owned(),
                    rect: bounds,
                    node_tag: node.variant_tag(),
                    color: modulate_color(base_color, node),
                });
                return;
            }
            for (i, child) in cs.iter().enumerate() {
                let idx = i as u32;
                let y = bounds.y + idx * slice_h;
                let h = if i + 1 == cs.len() {
                    (bounds.y + bounds.height) - y
                } else {
                    slice_h
                };
                layout_projected_boxes(
                    circle_id,
                    child,
                    Rect::new(bounds.x, y, bounds.width, h),
                    base_color,
                    out,
                );
            }
        }
        ViewNode::Row(cs) => {
            if cs.is_empty() {
                return;
            }
            let n = cs.len() as u32;
            let slice_w = bounds.width / n;
            if slice_w == 0 {
                out.push(CompiledOverlayBox {
                    circle_id: circle_id.to_owned(),
                    rect: bounds,
                    node_tag: node.variant_tag(),
                    color: modulate_color(base_color, node),
                });
                return;
            }
            for (i, child) in cs.iter().enumerate() {
                let idx = i as u32;
                let x = bounds.x + idx * slice_w;
                let w = if i + 1 == cs.len() {
                    (bounds.x + bounds.width) - x
                } else {
                    slice_w
                };
                layout_projected_boxes(
                    circle_id,
                    child,
                    Rect::new(x, bounds.y, w, bounds.height),
                    base_color,
                    out,
                );
            }
        }
        ViewNode::Section { children, .. } | ViewNode::Grid { children, .. } => {
            if children.is_empty() {
                out.push(CompiledOverlayBox {
                    circle_id: circle_id.to_owned(),
                    rect: bounds,
                    node_tag: node.variant_tag(),
                    color: modulate_color(base_color, node),
                });
            } else {
                layout_projected_boxes(
                    circle_id,
                    &ViewNode::VStack(children.clone()),
                    bounds,
                    base_color,
                    out,
                );
            }
        }
        ViewNode::Host {
            view: Some(inner), ..
        } => {
            layout_projected_boxes(circle_id, inner, bounds, base_color, out);
        }
        ViewNode::Adept(inner) => {
            layout_projected_boxes(circle_id, inner, bounds, base_color, out);
        }
        ViewNode::Tile { w, h, .. } => {
            let clamped_w = (*w).min(bounds.width);
            let clamped_h = (*h).min(bounds.height);
            if clamped_w > 0 && clamped_h > 0 {
                out.push(CompiledOverlayBox {
                    circle_id: circle_id.to_owned(),
                    rect: Rect::new(bounds.x, bounds.y, clamped_w, clamped_h),
                    node_tag: node.variant_tag(),
                    color: modulate_color(base_color, node),
                });
            }
        }
        other => {
            out.push(CompiledOverlayBox {
                circle_id: circle_id.to_owned(),
                rect: bounds,
                node_tag: other.variant_tag(),
                color: modulate_color(base_color, other),
            });
        }
    }
}

/// Scrub an untrusted belief-circle `ViewNode` through `Frustum`, reject hardware-chrome spoofing,
/// enforce `TrustedConsentBand` non-intrusion (`Refuse` or `ClipToSafeRegion`), and compile into
/// viewport-bounded overlay boxes.
pub fn compile_belief_view_node(
    viewport: Viewport,
    consent_band: TrustedConsentBand,
    frustum: &Frustum,
    world_state: &WorldState,
    spec: &BeliefOverlaySpec,
    policy: IntrusionPolicy,
) -> Result<CompiledBeliefOverlay, EpiphanyRefusal> {
    if viewport.is_empty()
        || consent_band.rect.is_empty()
        || !consent_band.rect.fits_within(viewport)
    {
        return Err(EpiphanyRefusal::InvalidGeometry {
            reason: "viewport and trusted consent band must be non-empty and in-bounds",
        });
    }
    let mut raw_count = 0usize;
    validate_belief_tree(&spec.circle_id, &spec.root, 0, &mut raw_count)?;

    let projected_tree = project_view_node(frustum, world_state, &spec.cell, &spec.root);
    let mut proj_count = 0usize;
    validate_belief_tree(&spec.circle_id, &projected_tree, 0, &mut proj_count)?;

    if spec.requested_rect.intersects(consent_band.rect) {
        match policy {
            IntrusionPolicy::Refuse => {
                return Err(EpiphanyRefusal::ChromeBandIntrusion {
                    circle_id: spec.circle_id.clone(),
                    attempted: spec.requested_rect,
                    reserved_band: consent_band.rect,
                });
            }
            IntrusionPolicy::ClipToSafeRegion => {}
        }
    }

    let safe_rect = spec
        .requested_rect
        .clip_excluding(consent_band.rect, viewport);
    let mut boxes = Vec::new();
    if let Some(bounds) = safe_rect {
        layout_projected_boxes(
            &spec.circle_id,
            &projected_tree,
            bounds,
            spec.fill_color,
            &mut boxes,
        );
    }

    Ok(CompiledBeliefOverlay {
        circle_id: spec.circle_id.clone(),
        safe_rect,
        projected_tree,
        boxes,
    })
}

/// Lowest-priority scanout plane holding rasterized third-party belief-circle pixels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UntrustedBeliefPlane {
    pub viewport: Viewport,
    pub pixels: Vec<Rgba>,
}

impl UntrustedBeliefPlane {
    pub fn blank(viewport: Viewport) -> Result<Self, EpiphanyRefusal> {
        let len = viewport
            .pixel_count()
            .ok_or(EpiphanyRefusal::InvalidGeometry {
                reason: "viewport pixel count overflow",
            })?;
        Ok(Self {
            viewport,
            pixels: vec![Rgba::TRANSPARENT; len],
        })
    }

    pub fn from_pixels(viewport: Viewport, pixels: Vec<Rgba>) -> Result<Self, EpiphanyRefusal> {
        let expected = viewport
            .pixel_count()
            .ok_or(EpiphanyRefusal::InvalidGeometry {
                reason: "viewport pixel count overflow",
            })?;
        if pixels.len() != expected {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "untrusted belief plane buffer length mismatch",
            });
        }
        Ok(Self { viewport, pixels })
    }

    /// Rasterize compiled belief overlays in order using exact integer Porter-Duff `over`.
    pub fn rasterize_overlays(
        viewport: Viewport,
        overlays: &[CompiledBeliefOverlay],
    ) -> Result<Self, EpiphanyRefusal> {
        let mut plane = Self::blank(viewport)?;
        for overlay in overlays {
            for b in &overlay.boxes {
                if !b.rect.fits_within(viewport) {
                    return Err(EpiphanyRefusal::InvalidGeometry {
                        reason: "compiled overlay box out of viewport bounds",
                    });
                }
                let x_end = b.rect.x + b.rect.width;
                let y_end = b.rect.y + b.rect.height;
                for y in b.rect.y..y_end {
                    for x in b.rect.x..x_end {
                        if let Some(idx) = viewport.pixel_index(x, y) {
                            plane.pixels[idx] = porter_duff_over(b.color, plane.pixels[idx]);
                        }
                    }
                }
            }
        }
        Ok(plane)
    }

    pub fn pixel_at(&self, x: u32, y: u32) -> Rgba {
        self.viewport
            .pixel_index(x, y)
            .and_then(|idx| self.pixels.get(idx).copied())
            .unwrap_or(Rgba::TRANSPARENT)
    }
}

// ---------------------------------------------------------------------------
// 3-Plane Scanout Compositor
// ---------------------------------------------------------------------------

/// Final scanout framebuffer emitted by `EpiphanyCompositor`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanoutFrame {
    pub viewport: Viewport,
    pub pixels: Vec<Rgba>,
}

impl ScanoutFrame {
    pub fn pixel_at(&self, x: u32, y: u32) -> Option<Rgba> {
        let idx = self.viewport.pixel_index(x, y)?;
        self.pixels.get(idx).copied()
    }
}

/// Exact single-pixel 3-plane scanout composition:
/// `TrustedConsentChromePlane` over (`PhysicalHazardReticlePlane` over `clipped(UntrustedBeliefPlane)`).
/// When `in_protected_chrome` is true (`TrustedConsentBand` or active `ConsentModalRect`),
/// the untrusted belief pixel is hard-zeroed prior to compositing.
pub const fn composite_pixel(
    untrusted: Rgba,
    hazard: Rgba,
    chrome: Rgba,
    in_protected_chrome: bool,
) -> Rgba {
    let clipped_untrusted = if in_protected_chrome {
        Rgba::TRANSPARENT
    } else {
        untrusted
    };
    let with_hazard = porter_duff_over(hazard, clipped_untrusted);
    porter_duff_over(chrome, with_hazard)
}

/// Hardware-enforced 3-plane Epiphany AR display scanout compositor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EpiphanyCompositor {
    pub viewport: Viewport,
}

impl EpiphanyCompositor {
    pub const fn new(viewport: Viewport) -> Self {
        Self { viewport }
    }

    pub fn composite_frame(
        &self,
        untrusted: &UntrustedBeliefPlane,
        hazards: &PhysicalHazardReticlePlane,
        chrome: &TrustedConsentChromePlane,
    ) -> Result<ScanoutFrame, EpiphanyRefusal> {
        if self.viewport.is_empty() {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "compositor viewport must be non-empty",
            });
        }
        if untrusted.viewport != self.viewport
            || hazards.viewport != self.viewport
            || chrome.viewport != self.viewport
        {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "all three scanout planes must share identical viewport dimensions",
            });
        }
        let expected_len = self
            .viewport
            .pixel_count()
            .ok_or(EpiphanyRefusal::InvalidGeometry {
                reason: "viewport pixel count overflow",
            })?;
        if untrusted.pixels.len() != expected_len {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "untrusted plane pixel buffer length mismatch",
            });
        }
        chrome.validate()?;
        hazards.validate()?;

        let mut pixels = Vec::with_capacity(expected_len);
        for y in 0..self.viewport.height {
            for x in 0..self.viewport.width {
                let in_protected = chrome.is_protected_pixel(x, y);
                let u = untrusted.pixel_at(x, y);
                let h = hazards.pixel_at(x, y);
                let c = chrome.pixel_at(x, y);
                pixels.push(composite_pixel(u, h, c, in_protected));
            }
        }
        Ok(ScanoutFrame {
            viewport: self.viewport,
            pixels,
        })
    }
}

// ---------------------------------------------------------------------------
// cSHAKE256 + LEB128 Framing
// ---------------------------------------------------------------------------

pub use obend_keccak::cshake256_32;
use obend_keccak::Cshake256;
pub use obend_primitives::ct::ct_eq_32 as ct_eq_digest;

fn push_leb128(buf: &mut Vec<u8>, mut n: u64) {
    loop {
        let mut byte = (n & 0x7f) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if n == 0 {
            break;
        }
    }
}

fn push_list_field(buf: &mut Vec<u8>, bytes: &[u8]) {
    push_leb128(buf, bytes.len() as u64);
    buf.extend_from_slice(bytes);
}

fn absorb_list_field(s: &mut Cshake256, bytes: &[u8]) {
    let mut len_buf = Vec::with_capacity(10);
    push_leb128(&mut len_buf, bytes.len() as u64);
    s.absorb(&len_buf);
    s.absorb(bytes);
}

// ---------------------------------------------------------------------------
// Monotone Counter-Bound CSI-2 Sensor Frame Sealer & ROI Redactor
// ---------------------------------------------------------------------------

/// A CSI-2 tile strip within a sensor frame. Global pixel coordinate at `pixels[idx]` is
/// `(tile_x + (idx % tile_w), tile_y + (idx / tile_w))`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SensorTile {
    pub tile_x: u32,
    pub tile_y: u32,
    pub tile_w: u32,
    pub tile_h: u32,
    pub pixels: Vec<Rgba>,
}

impl SensorTile {
    pub fn rect(&self) -> Rect {
        Rect::new(self.tile_x, self.tile_y, self.tile_w, self.tile_h)
    }

    pub fn validate(&self, frame_viewport: Viewport) -> Result<(), EpiphanyRefusal> {
        if self.tile_w == 0 || self.tile_h == 0 {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "sensor tile dimensions must be non-empty",
            });
        }
        if !self.rect().fits_within(frame_viewport) {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "sensor tile exceeds frame dimensions",
            });
        }
        let expected = Viewport::new(self.tile_w, self.tile_h)
            .pixel_count()
            .ok_or(EpiphanyRefusal::InvalidGeometry {
                reason: "sensor tile pixel count overflow",
            })?;
        if self.pixels.len() != expected {
            return Err(EpiphanyRefusal::InvalidGeometry {
                reason: "sensor tile pixel buffer length mismatch",
            });
        }
        Ok(())
    }

    pub fn encode_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 + self.pixels.len().saturating_mul(4));
        out.extend_from_slice(&self.tile_x.to_be_bytes());
        out.extend_from_slice(&self.tile_y.to_be_bytes());
        out.extend_from_slice(&self.tile_w.to_be_bytes());
        out.extend_from_slice(&self.tile_h.to_be_bytes());
        for px in &self.pixels {
            out.extend_from_slice(&px.to_bytes());
        }
        out
    }
}

/// Raw CSI-2 sensor frame prior to ROI redaction and cryptographic sealing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawSensorFrame {
    pub sensor_id: u64,
    pub mono_seq: u64,
    pub width: u32,
    pub height: u32,
    pub tiles: Vec<SensorTile>,
    pub redact_boxes: Vec<Rect>,
}

impl RawSensorFrame {
    /// Convenience constructor wrapping a single full-frame pixel buffer as 1 CSI-2 tile
    /// `(0, 0, width, height, pixels)`.
    pub fn from_full_frame(
        sensor_id: u64,
        mono_seq: u64,
        width: u32,
        height: u32,
        pixels: Vec<Rgba>,
        redact_boxes: Vec<Rect>,
    ) -> Self {
        Self {
            sensor_id,
            mono_seq,
            width,
            height,
            tiles: vec![SensorTile {
                tile_x: 0,
                tile_y: 0,
                tile_w: width,
                tile_h: height,
                pixels,
            }],
            redact_boxes,
        }
    }
}

/// Post-redaction sensor frame bound to a 256-bit `OBEND.SHE.SENSOR_SEAL/v1` commitment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedSensorFrame {
    pub sensor_id: u64,
    pub mono_seq: u64,
    pub width: u32,
    pub height: u32,
    pub redact_boxes: Vec<Rect>,
    pub redacted_tiles: Vec<SensorTile>,
    pub seal_digest: Digest,
}

/// Zero every pixel across all `tiles` whose global coordinate `(tile_x + idx % tile_w,
/// tile_y + idx / tile_w)` falls inside any `redact_box`.
pub fn redact_sensor_tiles(
    width: u32,
    height: u32,
    tiles: &[SensorTile],
    redact_boxes: &[Rect],
) -> Result<Vec<SensorTile>, EpiphanyRefusal> {
    let viewport = Viewport::new(width, height);
    if viewport.is_empty() {
        return Err(EpiphanyRefusal::InvalidGeometry {
            reason: "sensor frame dimensions must be non-empty",
        });
    }
    let mut out = Vec::with_capacity(tiles.len());
    for tile in tiles {
        tile.validate(viewport)?;
        let mut pixels = tile.pixels.clone();
        if tile.tile_w > 0 && tile.tile_h > 0 {
            let tw = tile.tile_w as usize;
            for (idx, px) in pixels.iter_mut().enumerate() {
                let lx = (idx % tw) as u32;
                let ly = (idx / tw) as u32;
                let gx = tile.tile_x + lx;
                let gy = tile.tile_y + ly;
                if redact_boxes.iter().any(|b| b.contains(gx, gy)) {
                    *px = Rgba::TRANSPARENT;
                }
            }
        }
        out.push(SensorTile {
            tile_x: tile.tile_x,
            tile_y: tile.tile_y,
            tile_w: tile.tile_w,
            tile_h: tile.tile_h,
            pixels,
        });
    }
    Ok(out)
}

fn encode_redact_boxes(redact_boxes: &[Rect]) -> Vec<u8> {
    let mut out = Vec::with_capacity(redact_boxes.len().saturating_mul(16));
    for b in redact_boxes {
        out.extend_from_slice(&b.x.to_be_bytes());
        out.extend_from_slice(&b.y.to_be_bytes());
        out.extend_from_slice(&b.width.to_be_bytes());
        out.extend_from_slice(&b.height.to_be_bytes());
    }
    out
}

fn encode_tiles_field(tiles: &[SensorTile]) -> Vec<u8> {
    let mut out = Vec::new();
    for tile in tiles {
        let encoded = tile.encode_bytes();
        push_list_field(&mut out, &encoded);
    }
    out
}

/// Canonical 6-field LEB128-length-framed preimage for `OBEND.SHE.SENSOR_SEAL/v1`, matching
/// `Obend.Polis.EpiphanyCompositor` byte-for-byte.
///
/// Field layout (`fields(xs)` concatenates `leb128(x.len) || x`):
/// 0. `u64_be(sensor_id)` (8 bytes)
/// 1. `u64_be(mono_seq)` (8 bytes)
/// 2. `u32_be(width)` (4 bytes)
/// 3. `u32_be(height)` (4 bytes)
/// 4. `redact_boxes` (`16 * N` bytes, each `Rect` = `be4(x) || be4(y) || be4(w) || be4(h)`)
/// 5. `fields(redacted_tiles.map(encode_tile))` where each tile is
///    `be4(tile_x) || be4(tile_y) || be4(tile_w) || be4(tile_h) || pixels_rgba`
pub fn encode_sensor_seal_preimage(
    sensor_id: u64,
    mono_seq: u64,
    width: u32,
    height: u32,
    redact_boxes: &[Rect],
    redacted_tiles: &[SensorTile],
) -> Vec<u8> {
    let boxes_bytes = encode_redact_boxes(redact_boxes);
    let tiles_bytes = encode_tiles_field(redacted_tiles);

    let mut preimage = Vec::with_capacity(64 + boxes_bytes.len() + tiles_bytes.len());
    push_list_field(&mut preimage, &sensor_id.to_be_bytes());
    push_list_field(&mut preimage, &mono_seq.to_be_bytes());
    push_list_field(&mut preimage, &width.to_be_bytes());
    push_list_field(&mut preimage, &height.to_be_bytes());
    push_list_field(&mut preimage, &boxes_bytes);
    push_list_field(&mut preimage, &tiles_bytes);
    preimage
}

/// Compute the 32-byte `OBEND.SHE.SENSOR_SEAL/v1` `cSHAKE256` commitment over a post-redaction
/// sensor frame (explicit 6-field LEB128 streaming absorption).
pub fn compute_sensor_seal(
    sensor_id: u64,
    mono_seq: u64,
    width: u32,
    height: u32,
    redact_boxes: &[Rect],
    redacted_tiles: &[SensorTile],
) -> Digest {
    let boxes_bytes = encode_redact_boxes(redact_boxes);
    let tiles_bytes = encode_tiles_field(redacted_tiles);
    let mut s = Cshake256::customized(SENSOR_SEAL_DOMAIN.as_bytes());
    absorb_list_field(&mut s, &sensor_id.to_be_bytes());
    absorb_list_field(&mut s, &mono_seq.to_be_bytes());
    absorb_list_field(&mut s, &width.to_be_bytes());
    absorb_list_field(&mut s, &height.to_be_bytes());
    absorb_list_field(&mut s, &boxes_bytes);
    absorb_list_field(&mut s, &tiles_bytes);
    let mut out = [0u8; 32];
    s.squeeze(&mut out);
    out
}

/// Verify that a `SealedSensorFrame` has valid geometry, optionally clears a strictly monotone
/// lower bound, contains zero non-transparent pixels inside every `redact_box` across all tiles,
/// and matches its `OBEND.SHE.SENSOR_SEAL/v1` digest in constant time.
pub fn verify_sealed_frame(
    frame: &SealedSensorFrame,
    last_seq: Option<u64>,
) -> Result<(), EpiphanyRefusal> {
    if let Some(prev) = last_seq {
        if frame.mono_seq <= prev {
            return Err(EpiphanyRefusal::SensorSeqRollback {
                sensor_id: frame.sensor_id,
                last_seq: prev,
                attempted_seq: frame.mono_seq,
            });
        }
    }
    if frame.mono_seq == u64::MAX {
        return Err(EpiphanyRefusal::SensorSeqOverflow {
            sensor_id: frame.sensor_id,
            attempted_seq: frame.mono_seq,
        });
    }
    let viewport = Viewport::new(frame.width, frame.height);
    if viewport.is_empty() {
        return Err(EpiphanyRefusal::InvalidGeometry {
            reason: "sealed sensor frame dimensions must be non-empty",
        });
    }
    for (tile_index, tile) in frame.redacted_tiles.iter().enumerate() {
        tile.validate(viewport)?;
        if tile.tile_w == 0 || tile.tile_h == 0 {
            continue;
        }
        let tw = tile.tile_w as usize;
        for (idx, px) in tile.pixels.iter().enumerate() {
            let gx = tile.tile_x + (idx % tw) as u32;
            let gy = tile.tile_y + (idx / tw) as u32;
            for (box_index, b) in frame.redact_boxes.iter().enumerate() {
                if b.contains(gx, gy) && *px != Rgba::TRANSPARENT {
                    return Err(EpiphanyRefusal::UnredactedPrivateRoi {
                        tile_index,
                        box_index,
                        x: gx,
                        y: gy,
                    });
                }
            }
        }
    }
    let recomputed = compute_sensor_seal(
        frame.sensor_id,
        frame.mono_seq,
        frame.width,
        frame.height,
        &frame.redact_boxes,
        &frame.redacted_tiles,
    );
    if !ct_eq_digest(&frame.seal_digest, &recomputed) {
        return Err(EpiphanyRefusal::SealDigestMismatch {
            expected: recomputed,
            actual: frame.seal_digest,
        });
    }
    Ok(())
}

/// Stateful per-sensor monotone counter-bound CSI-2 frame redactor & sealer.
#[derive(Debug, Clone, Default)]
pub struct SensorFrameSealer {
    last_seq_by_sensor: BTreeMap<u64, u64>,
}

impl SensorFrameSealer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn last_seq(&self, sensor_id: u64) -> Option<u64> {
        self.last_seq_by_sensor.get(&sensor_id).copied()
    }

    /// Enforce strict per-sensor monotonicity (`mono_seq > last_seq`), refuse `u64::MAX`
    /// overflow/wraparound, zero every pixel inside `frame.redact_boxes`, and seal the redacted
    /// frame under `OBEND.SHE.SENSOR_SEAL/v1`.
    pub fn seal_frame(
        &mut self,
        frame: &RawSensorFrame,
    ) -> Result<SealedSensorFrame, EpiphanyRefusal> {
        if let Some(&prev) = self.last_seq_by_sensor.get(&frame.sensor_id) {
            if frame.mono_seq <= prev {
                return Err(EpiphanyRefusal::SensorSeqRollback {
                    sensor_id: frame.sensor_id,
                    last_seq: prev,
                    attempted_seq: frame.mono_seq,
                });
            }
        }
        if frame.mono_seq == u64::MAX {
            return Err(EpiphanyRefusal::SensorSeqOverflow {
                sensor_id: frame.sensor_id,
                attempted_seq: frame.mono_seq,
            });
        }
        let redacted_tiles =
            redact_sensor_tiles(frame.width, frame.height, &frame.tiles, &frame.redact_boxes)?;
        let seal_digest = compute_sensor_seal(
            frame.sensor_id,
            frame.mono_seq,
            frame.width,
            frame.height,
            &frame.redact_boxes,
            &redacted_tiles,
        );
        self.last_seq_by_sensor
            .insert(frame.sensor_id, frame.mono_seq);
        Ok(SealedSensorFrame {
            sensor_id: frame.sensor_id,
            mono_seq: frame.mono_seq,
            width: frame.width,
            height: frame.height,
            redact_boxes: frame.redact_boxes.clone(),
            redacted_tiles,
            seal_digest,
        })
    }

    /// Verify a multi-frame stream of already-sealed frames for per-sensor strict monotonicity,
    /// complete ROI redaction, and `OBEND.SHE.SENSOR_SEAL/v1` digest integrity.
    pub fn verify_sealed_trace(frames: &[SealedSensorFrame]) -> Result<(), EpiphanyRefusal> {
        let mut seen: BTreeMap<u64, u64> = BTreeMap::new();
        for frame in frames {
            let prev = seen.get(&frame.sensor_id).copied();
            verify_sealed_frame(frame, prev)?;
            seen.insert(frame.sensor_id, frame.mono_seq);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Software Reference Mirrors of Open-FPGA Inline RTL Gates (`EmitSv` / `YosysLec`)
// (Bit-exact parity with `Obend.Polis.EpiphanyCompositor` §6)
// ---------------------------------------------------------------------------

/// Pack an `Rgba` pixel into a 32-bit RGBA8888 word inside the 64-bit `RtlModule` carrier
/// (`r | (g << 8) | (b << 16) | (a << 24)`), matching Lean `packRgba32`.
pub const fn pack_rgba32(p: Rgba) -> u64 {
    (p.r as u64) | ((p.g as u64) << 8) | ((p.b as u64) << 16) | ((p.a as u64) << 24)
}

/// Unpack the low 32 bits of a 64-bit RTL pixel word into `Rgba`.
pub const fn unpack_rgba32(word: u64) -> Rgba {
    Rgba::new(
        (word & 0xFF) as u8,
        ((word >> 8) & 0xFF) as u8,
        ((word >> 16) & 0xFF) as u8,
        ((word >> 24) & 0xFF) as u8,
    )
}

/// Software cycle-exact reference mirror of `scanline_consent_mux` (`scanlineConsentMuxRtl`).
/// Models the synthesizable 1-cycle pipelined open-FPGA mux (`py < consent_height ? chrome : belief`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ScanlineConsentMuxRtlModel {
    pub out_pixel_q: u64,
    pub in_band_q: u64,
}

impl ScanlineConsentMuxRtlModel {
    pub const fn new() -> Self {
        Self {
            out_pixel_q: 0,
            in_band_q: 0,
        }
    }

    /// Combinational output (`comb_pixel`) matching `evalModuleOutputs scanlineConsentMuxRtl`.
    pub const fn eval_comb(
        py: u16,
        consent_height: u16,
        chrome_pixel: u32,
        belief_pixel: u32,
    ) -> u64 {
        if py < consent_height {
            chrome_pixel as u64
        } else {
            belief_pixel as u64
        }
    }

    /// Synchronous rising-edge register step matching `stepModuleRegs scanlineConsentMuxRtl`.
    pub fn step_clock(
        &mut self,
        rst: bool,
        py: u16,
        consent_height: u16,
        chrome_pixel: u32,
        belief_pixel: u32,
    ) {
        if rst {
            self.out_pixel_q = 0;
            self.in_band_q = 0;
        } else if py < consent_height {
            self.out_pixel_q = chrome_pixel as u64;
            self.in_band_q = 1;
        } else {
            self.out_pixel_q = belief_pixel as u64;
            self.in_band_q = 0;
        }
    }
}

/// Software cycle-exact reference mirror of `camera_scanline_roi_zeroer` (`cameraScanlineRoiZeroerRtl`).
/// Models the synthesizable 1-cycle pipelined open-FPGA ROI zeroer (`[roi_x0, roi_x1) x [roi_y0, roi_y1)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CameraScanlineRoiZeroerRtlModel {
    pub cap_pixel_q: u64,
    pub redacted_q: u64,
}

impl CameraScanlineRoiZeroerRtlModel {
    pub const fn new() -> Self {
        Self {
            cap_pixel_q: 0,
            redacted_q: 0,
        }
    }

    pub const fn in_roi_box(
        px: u16,
        py: u16,
        roi_x0: u16,
        roi_x1: u16,
        roi_y0: u16,
        roi_y1: u16,
    ) -> bool {
        px >= roi_x0 && px < roi_x1 && py >= roi_y0 && py < roi_y1
    }

    /// Combinational output (`comb_scrubbed_pixel`) matching `evalModuleOutputs cameraScanlineRoiZeroerRtl`.
    pub const fn eval_comb(
        px: u16,
        py: u16,
        roi_x0: u16,
        roi_x1: u16,
        roi_y0: u16,
        roi_y1: u16,
        raw_pixel: u32,
    ) -> u64 {
        if Self::in_roi_box(px, py, roi_x0, roi_x1, roi_y0, roi_y1) {
            0
        } else {
            raw_pixel as u64
        }
    }

    /// Synchronous rising-edge register step matching `stepModuleRegs cameraScanlineRoiZeroerRtl`.
    #[allow(clippy::too_many_arguments)]
    pub fn step_clock(
        &mut self,
        rst: bool,
        px: u16,
        py: u16,
        roi_x0: u16,
        roi_x1: u16,
        roi_y0: u16,
        roi_y1: u16,
        raw_pixel: u32,
    ) {
        if rst {
            self.cap_pixel_q = 0;
            self.redacted_q = 0;
        } else if Self::in_roi_box(px, py, roi_x0, roi_x1, roi_y0, roi_y1) {
            self.cap_pixel_q = 0;
            self.redacted_q = 1;
        } else {
            self.cap_pixel_q = raw_pixel as u64;
            self.redacted_q = 0;
        }
    }
}

// ---------------------------------------------------------------------------
// Pure Software Streaming Scanline Sealer (`OBEND.SHE.SENSOR_SEAL/v1`)
// (Byte-exact parity with `Obend.Polis.EpiphanyCompositor` §7 — untrusted I/O)
// ---------------------------------------------------------------------------

/// A single raw camera scanline packet arriving over an untrusted external I/O stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanlinePacket {
    pub line_y: u32,
    pub start_x: u32,
    pub width: u32,
    pub raw_pixels: Vec<Rgba>,
}

/// Immutable per-frame configuration pinned at `begin_frame` before any scanline is accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanlineStreamConfig {
    pub sensor_id: u64,
    pub mono_seq: u64,
    pub frame_width: u32,
    pub frame_height: u32,
    pub redact_boxes: Vec<Rect>,
}

/// Pure software streaming scanline redactor and `OBEND.SHE.SENSOR_SEAL/v1` frame sealer.
/// External camera streams are treated strictly as untrusted I/O; private ROI pixels are zeroed
/// per scanline against the pinned `active_cfg.redact_boxes`, full contiguous scanline coverage is
/// enforced at `finalize_and_seal`, and `u64::MAX` / replay / unfinished-frame seq reuse are refused.
#[derive(Debug, Clone)]
pub struct ScanlineStreamSealer {
    active_cfg: Option<ScanlineStreamConfig>,
    assembled_tiles: Vec<SensorTile>,
    sealer: SensorFrameSealer,
    started_seq_by_sensor: BTreeMap<u64, u64>,
}

impl Default for ScanlineStreamSealer {
    fn default() -> Self {
        Self::new()
    }
}

impl ScanlineStreamSealer {
    pub fn new() -> Self {
        Self {
            active_cfg: None,
            assembled_tiles: Vec::new(),
            sealer: SensorFrameSealer::new(),
            started_seq_by_sensor: BTreeMap::new(),
        }
    }

    pub fn assembled_tiles(&self) -> &[SensorTile] {
        &self.assembled_tiles
    }

    pub fn sealer(&self) -> &SensorFrameSealer {
        &self.sealer
    }

    /// Reset active frame buffers while preserving `sealer` and `started_seq_by_sensor` guards.
    pub fn reset_frame(&mut self) {
        self.active_cfg = None;
        self.assembled_tiles.clear();
    }

    /// Pin an immutable `ScanlineStreamConfig` for the next monotone capture frame.
    /// Refuses `u64::MAX`, sequence rollback, and restarting an unfinished frame under the same
    /// `(sensor_id, mono_seq)`.
    pub fn begin_frame(&mut self, cfg: ScanlineStreamConfig) -> Result<(), EpiphanyRefusal> {
        let vp = Viewport::new(cfg.frame_width, cfg.frame_height);
        if vp.is_empty() {
            return Err(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "stream frame dimensions must be strictly positive",
            });
        }
        if cfg.mono_seq == u64::MAX {
            return Err(EpiphanyRefusal::SensorSeqOverflow {
                sensor_id: cfg.sensor_id,
                attempted_seq: cfg.mono_seq,
            });
        }
        let highest = self
            .sealer
            .last_seq(cfg.sensor_id)
            .into_iter()
            .chain(self.started_seq_by_sensor.get(&cfg.sensor_id).copied())
            .max();
        if let Some(prev) = highest {
            if cfg.mono_seq <= prev {
                return Err(EpiphanyRefusal::SensorSeqRollback {
                    sensor_id: cfg.sensor_id,
                    last_seq: prev,
                    attempted_seq: cfg.mono_seq,
                });
            }
        }
        self.reset_frame();
        self.started_seq_by_sensor
            .insert(cfg.sensor_id, cfg.mono_seq);
        self.active_cfg = Some(cfg);
        Ok(())
    }

    /// Ingest one raw scanline packet, scrub pixels inside pinned `active_cfg.redact_boxes` to
    /// `Rgba::TRANSPARENT`, and append the post-redaction tile.
    pub fn step_scanline(&mut self, pkt: &ScanlinePacket) -> Result<&SensorTile, EpiphanyRefusal> {
        let cfg = self
            .active_cfg
            .as_ref()
            .ok_or(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "scanline stream frame not initialized via begin_frame",
            })?;
        if pkt.width == 0
            || pkt.line_y >= cfg.frame_height
            || pkt
                .start_x
                .checked_add(pkt.width)
                .is_none_or(|e| e > cfg.frame_width)
            || pkt.raw_pixels.len() != pkt.width as usize
        {
            return Err(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "malformed scanline packet geometry",
            });
        }
        if self.assembled_tiles.iter().any(|t| t.tile_y == pkt.line_y) {
            return Err(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "duplicate scanline line_y within active frame",
            });
        }

        let mut scrubbed = Vec::with_capacity(pkt.raw_pixels.len());
        for (idx, &px) in pkt.raw_pixels.iter().enumerate() {
            let gx = pkt.start_x + idx as u32;
            let gy = pkt.line_y;
            let out_px = if cfg.redact_boxes.iter().any(|b| b.contains(gx, gy)) {
                Rgba::TRANSPARENT
            } else {
                px
            };
            scrubbed.push(out_px);
        }

        self.assembled_tiles.push(SensorTile {
            tile_x: pkt.start_x,
            tile_y: pkt.line_y,
            tile_w: pkt.width,
            tile_h: 1,
            pixels: scrubbed,
        });
        Ok(self.assembled_tiles.last().expect("pushed scanline tile"))
    }

    /// Finalize the post-redaction scanline tiles into a `OBEND.SHE.SENSOR_SEAL/v1` sealed frame,
    /// enforcing complete contiguous scanline coverage (`y = 0..frame_height`, `start_x = 0`,
    /// `width = frame_width`) and strict per-sensor monotonicity + `u64::MAX` refusal.
    pub fn finalize_and_seal(&mut self) -> Result<SealedSensorFrame, EpiphanyRefusal> {
        let cfg = self
            .active_cfg
            .as_ref()
            .ok_or(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "scanline stream frame not initialized via begin_frame",
            })?
            .clone();
        let expected_lines = cfg.frame_height as usize;
        let complete = self.assembled_tiles.len() == expected_lines
            && self.assembled_tiles.iter().enumerate().all(|(y, t)| {
                t.tile_x == 0
                    && t.tile_y == y as u32
                    && t.tile_w == cfg.frame_width
                    && t.tile_h == 1
            });
        if !complete {
            return Err(EpiphanyRefusal::ScanlineStreamViolation {
                reason: "incomplete scanline frame coverage",
            });
        }
        let frame = RawSensorFrame {
            sensor_id: cfg.sensor_id,
            mono_seq: cfg.mono_seq,
            width: cfg.frame_width,
            height: cfg.frame_height,
            tiles: self.assembled_tiles.clone(),
            redact_boxes: cfg.redact_boxes.clone(),
        };
        let sealed = self.sealer.seal_frame(&frame)?;
        self.active_cfg = None;
        self.assembled_tiles.clear();
        Ok(sealed)
    }
}

/// Verify a `SealedSensorFrame` against an externally trusted policy `required_redact_boxes`
/// (preventing a malicious producer from stripping `redact_boxes` to `[]` before sealing).
pub fn verify_sealed_frame_against_policy(
    frame: &SealedSensorFrame,
    required_redact_boxes: &[Rect],
    last_seq: Option<u64>,
) -> Result<(), EpiphanyRefusal> {
    if frame.redact_boxes != required_redact_boxes {
        return Err(EpiphanyRefusal::InvalidGeometry {
            reason: "sealed frame redact_boxes does not match trusted policy ROI",
        });
    }
    verify_sealed_frame(frame, last_seq)
}
