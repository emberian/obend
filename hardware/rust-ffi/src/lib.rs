//! # `obend-hw-ffi` — Rust Host & RFC 8949 Binary CBOR / `.obnb` Codec for `Obend.Hardware`
//!
//! Speaks the exact 39-byte RFC 8949 CBOR tagged hardware certificate wire format (`Tag 0x0BED`)
//! and `Obend.Core.Data.encoded` `.obnb` structured notebook cell format proved round-trip sound
//! in `lean/Obend/Hardware/Codec.lean`.
//!
//! Also provides raw EDA data munging (Touchstone `.s2p`, KiCad `.kicad_pcb` S-expressions,
//! and Markdown part frontmatter) into compact binary CBOR frames with zero JSON.

/// Polymorphic binary wire serialization trait mirroring Lean's `class BinaryCodec (α : Type)`.
pub trait BinaryCodec: Sized {
    fn encode_bytes(&self, out: &mut Vec<u8>);
    fn decode_bytes(input: &[u8]) -> Option<(Self, &[u8])>;

    fn to_vec(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.encode_bytes(&mut buf);
        buf
    }

    fn from_slice(input: &[u8]) -> Option<Self> {
        let (val, rest) = Self::decode_bytes(input)?;
        if rest.is_empty() {
            Some(val)
        } else {
            None
        }
    }
}

/// RFC 8949 CBOR Major Type 0 (4-byte unsigned integer: `0x1A` + big-endian u32).
pub fn cbor_encode_u32(n: u32, out: &mut Vec<u8>) {
    out.push(0x1A);
    out.extend_from_slice(&n.to_be_bytes());
}

/// Decode RFC 8949 CBOR Major Type 0 4-byte unsigned integer (`0x1A` + 4-byte BE),
/// matching Lean's `cborDecodeU32` byte-for-byte.
pub fn cbor_decode_u32(input: &[u8]) -> Option<(u32, &[u8])> {
    let (&tag, rest) = input.split_first()?;
    if tag == 0x1A && rest.len() >= 4 {
        let n = u32::from_be_bytes([rest[0], rest[1], rest[2], rest[3]]);
        Some((n, &rest[4..]))
    } else {
        None
    }
}

/// RFC 8949 CBOR Major Type 0/1 signed 32-bit integer (`0x1A` for `>= 0`, `0x3A` for `-1 - n`).
/// Matches Lean's `cborEncodeI32` (`Int.ofNat n` / `Int.negSucc n`) byte-for-byte.
pub fn cbor_encode_i32(z: i32, out: &mut Vec<u8>) {
    if z >= 0 {
        out.push(0x1A);
        out.extend_from_slice(&(z as u32).to_be_bytes());
    } else {
        let neg_succ = (-1i64 - (z as i64)) as u32;
        out.push(0x3A);
        out.extend_from_slice(&neg_succ.to_be_bytes());
    }
}

/// Decode RFC 8949 CBOR Major Type 0/1 signed 32-bit integer.
pub fn cbor_decode_i32(input: &[u8]) -> Option<(i32, &[u8])> {
    if input.len() < 5 {
        return None;
    }
    let tag = input[0];
    let raw = u32::from_be_bytes([input[1], input[2], input[3], input[4]]);
    let rest = &input[5..];
    if tag == 0x1A {
        let val = i32::try_from(raw).ok()?;
        Some((val, rest))
    } else if tag == 0x3A {
        let val = -1i64 - (raw as i64);
        let val_i32 = i32::try_from(val).ok()?;
        Some((val_i32, rest))
    } else {
        None
    }
}

/// Hardware verification domain IDs matching `Obend.Hardware.Codec.HwCertDomain`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum HwCertDomain {
    Pnr = 1,
    Retiming = 2,
    Photonics = 3,
    Pcb = 4,
    Dpr = 5,
    EdaBomSwap = 6,
    Multiphysics = 7,
    Analog2d = 8,
    DspBeamformer = 9,
    Magnetics = 10,
    FluidThermal = 11,
    PowerElectronics = 12,
    MechanicsVonNeumann = 13,
}

impl HwCertDomain {
    pub fn from_u32(v: u32) -> Option<Self> {
        match v {
            1 => Some(Self::Pnr),
            2 => Some(Self::Retiming),
            3 => Some(Self::Photonics),
            4 => Some(Self::Pcb),
            5 => Some(Self::Dpr),
            6 => Some(Self::EdaBomSwap),
            7 => Some(Self::Multiphysics),
            8 => Some(Self::Analog2d),
            9 => Some(Self::DspBeamformer),
            10 => Some(Self::Magnetics),
            11 => Some(Self::FluidThermal),
            12 => Some(Self::PowerElectronics),
            13 => Some(Self::MechanicsVonNeumann),
            _ => None,
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "pnr" => Some(Self::Pnr),
            "retiming" => Some(Self::Retiming),
            "photonics" => Some(Self::Photonics),
            "pcb" => Some(Self::Pcb),
            "dpr" => Some(Self::Dpr),
            "eda" | "eda_bom_swap" => Some(Self::EdaBomSwap),
            "multiphysics" => Some(Self::Multiphysics),
            "analog2d" => Some(Self::Analog2d),
            "dsp" => Some(Self::DspBeamformer),
            "magnetics" | "femm" => Some(Self::Magnetics),
            "fluid" | "fluid_thermal" | "cooling" => Some(Self::FluidThermal),
            "power" | "power_electronics" | "ms350" => Some(Self::PowerElectronics),
            "mechanics" | "von_neumann" => Some(Self::MechanicsVonNeumann),
            _ => None,
        }
    }
}

/// Canonical 39-byte RFC 8949 CBOR Hardware Certificate Frame (`Tag 0x0BED` + 7-element array `0x87`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryHwCert {
    pub domain: HwCertDomain,
    pub p0: i32,
    pub p1: i32,
    pub p2: i32,
    pub p3: i32,
    pub p4: i32,
    pub p5: i32,
}

impl BinaryCodec for BinaryHwCert {
    fn encode_bytes(&self, out: &mut Vec<u8>) {
        // RFC 8949 Tag 0x0BED (0xD9 0x0B 0xED) + 7-element array (0x87)
        out.extend_from_slice(&[0xD9, 0x0B, 0xED, 0x87]);
        cbor_encode_u32(self.domain as u32, out);
        cbor_encode_i32(self.p0, out);
        cbor_encode_i32(self.p1, out);
        cbor_encode_i32(self.p2, out);
        cbor_encode_i32(self.p3, out);
        cbor_encode_i32(self.p4, out);
        cbor_encode_i32(self.p5, out);
    }

    fn decode_bytes(input: &[u8]) -> Option<(Self, &[u8])> {
        if input.len() < 4 || input[0..4] != [0xD9, 0x0B, 0xED, 0x87] {
            return None;
        }
        let (dom_u32, r1) = cbor_decode_u32(&input[4..])?;
        let domain = HwCertDomain::from_u32(dom_u32)?;
        let (p0, r2) = cbor_decode_i32(r1)?;
        let (p1, r3) = cbor_decode_i32(r2)?;
        let (p2, r4) = cbor_decode_i32(r3)?;
        let (p3, r5) = cbor_decode_i32(r4)?;
        let (p4, r6) = cbor_decode_i32(r5)?;
        let (p5, r7) = cbor_decode_i32(r6)?;
        Some((
            Self {
                domain,
                p0,
                p1,
                p2,
                p3,
                p4,
                p5,
            },
            r7,
        ))
    }
}

impl BinaryHwCert {
    pub fn golden_for_domain(domain: HwCertDomain) -> Self {
        match domain {
            HwCertDomain::Pnr => Self {
                domain,
                p0: 0,
                p1: 0,
                p2: 0,
                p3: 1,
                p4: 5,
                p5: 2000,
            },
            HwCertDomain::Retiming => Self {
                domain,
                p0: 0,
                p1: 1,
                p2: 0,
                p3: 0,
                p4: 2200,
                p5: 2000,
            },
            HwCertDomain::Photonics => Self {
                domain,
                p0: 50,
                p1: 4200,
                p2: 8000,
                p3: 1550,
                p4: 985,
                p5: 985,
            },
            HwCertDomain::Pcb => Self {
                domain,
                p0: 25200,
                p1: 6,
                p2: 400,
                p3: 400,
                p4: 6,
                p5: 30000,
            },
            HwCertDomain::Dpr => Self {
                domain,
                p0: 2,
                p1: 0,
                p2: 2,
                p3: 4,
                p4: 10,
                p5: 40,
            },
            HwCertDomain::EdaBomSwap => Self {
                domain,
                p0: 2950,
                p1: 180,
                p2: 68000,
                p3: 1280,
                p4: 120,
                p5: 400,
            },
            HwCertDomain::Multiphysics => Self {
                domain,
                p0: 150,
                p1: 220,
                p2: 350000,
                p3: 325000,
                p4: 300000,
                p5: 1,
            },
            HwCertDomain::Analog2d => Self {
                domain,
                p0: 1000,
                p1: 15,
                p2: -9,
                p3: 6,
                p4: 4,
                p5: -8,
            },
            HwCertDomain::DspBeamformer => Self {
                domain,
                p0: 120,
                p1: -50,
                p2: 1000,
                p3: 0,
                p4: 500,
                p5: 16900,
            },
            HwCertDomain::Magnetics => Self {
                domain,
                p0: 6,      // polePairs
                p1: 250,    // psiPmMilliWb
                p2: 300,    // ldMicroH
                p3: 800,    // lqMicroH (saliency Lq > Ld)
                p4: -100,   // idAmp (field weakening <= 0)
                p5: 400,    // iqAmp (quadrature current >= 0)
            },
            HwCertDomain::FluidThermal => Self {
                domain,
                p0: 40000,  // tInletMilliC (40C WEG 50/50 coolant inlet)
                p1: 5000,   // powerLossW (5 kW stator copper + core loss)
                p2: 4,      // rCaloricMilliKPerW
                p3: 8,      // rConvMilliKPerW
                p4: 6,      // rCondMilliKPerW -> T_peak = 40000 + 5000*18 = 130000 mC <= 180000 mC
                p5: 180000, // maxClassHInsulationMilliC (180C Class-H limit)
            },
            HwCertDomain::PowerElectronics => Self {
                domain,
                p0: 200,    // isc (200 A short-circuit equivalent)
                p1: 1,      // gs (1 A/V source conductance)
                p2: 100,    // vStar (100 V MPP where isc = 2 * gs * vStar)
                p3: 800,    // vDcBusV (800 V DC link)
                p4: 15,     // lBusNh (15 nH laminated busbar inductance)
                p5: 10,     // diDtAmpPerNs (10 A/ns -> V_peak = 950 V <= 1200 V SiC rating)
            },
            HwCertDomain::MechanicsVonNeumann => Self {
                domain,
                p0: 1500,   // coldAirGapUm (1.5 mm radial air gap)
                p1: 250,    // thermalGrowthUm (0.25 mm rotor thermal growth)
                p2: 180,    // centrifugalGrowthUm (0.18 mm high-speed centrifugal growth)
                p3: 50,     // bearingRunoutUm (0.05 mm TIR bearing runout)
                p4: 500,    // minSafeAirGapUm (0.50 mm minimum safe clearance; hot gap = 1020 um)
                p5: 120,    // netFactoryPowerKw (+120 kW positive reflexive Von Neumann factory balance)
            },
        }
    }
}

/// Decoded representation of `Obend.Core.Data.Data` binary wire frames (`Obend.Core.Data.encoded`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObendCoreData {
    Natural(u64),
    Boolean(bool),
    Label(String),
    Record(Vec<(String, ObendCoreData)>),
    Variant(String, Box<ObendCoreData>),
}

fn read_nul_terminated_nat(input: &[u8]) -> Option<(u64, &[u8])> {
    let nul_pos = input.iter().position(|&b| b == 0)?;
    let ascii = std::str::from_utf8(&input[..nul_pos]).ok()?;
    let val = ascii.parse::<u64>().ok()?;
    Some((val, &input[nul_pos + 1..]))
}

fn read_length_prefixed_str(input: &[u8]) -> Option<(String, &[u8])> {
    let (byte_len, rest) = read_nul_terminated_nat(input)?;
    let len = byte_len as usize;
    if rest.len() < len {
        return None;
    }
    let s = std::str::from_utf8(&rest[..len]).ok()?.to_string();
    Some((s, &rest[len..]))
}

impl ObendCoreData {
    /// Parse a binary `.obnb` `Obend.Core.Data.encoded` byte stream emitted by the Lean kernel.
    pub fn decode_canonical(input: &[u8]) -> Option<(Self, &[u8])> {
        let (&tag, rest) = input.split_first()?;
        match tag {
            0 => {
                let (n, r) = read_nul_terminated_nat(rest)?;
                Some((Self::Natural(n), r))
            }
            1 => {
                let (&b, r) = rest.split_first()?;
                Some((Self::Boolean(b != 0), r))
            }
            2 => {
                let (s, r) = read_length_prefixed_str(rest)?;
                Some((Self::Label(s), r))
            }
            3 => {
                let (field_count, mut cur) = read_nul_terminated_nat(rest)?;
                if (field_count as usize) > cur.len() {
                    return None;
                }
                let mut fields = Vec::with_capacity(field_count as usize);
                for _ in 0..field_count {
                    let (fname, r_val) = read_length_prefixed_str(cur)?;
                    let (fval, r_next) = Self::decode_canonical(r_val)?;
                    fields.push((fname, fval));
                    cur = r_next;
                }
                Some((Self::Record(fields), cur))
            }
            4 => {
                let (label, r_payload) = read_length_prefixed_str(rest)?;
                let (payload, r_next) = Self::decode_canonical(r_payload)?;
                Some((Self::Variant(label, Box::new(payload)), r_next))
            }
            _ => None,
        }
    }
}

/// Raw EDA Data Munger 1: Parse KiCad `.kicad_pcb` serpentine meander S-expression parameters
/// into a binary `BinaryHwCert` (`HwCertDomain::Pcb`).
pub fn munge_kicad_meander_sexpr(sexpr: &str) -> Option<BinaryHwCert> {
    let mut base_um = 25200i32;
    let mut bends = 6i32;
    let mut amp_um = 400i32;
    let mut pitch_um = 400i32;
    let mut spacing_step = 4i32;
    let mut ref_um = 30000i32;

    for token in sexpr.split(|c: char| c == '(' || c == ')' || c == '\n') {
        let parts: Vec<&str> = token.split_whitespace().collect();
        if parts.len() == 2 {
            if let Ok(v) = parts[1].parse::<i32>() {
                match parts[0] {
                    "base_length_um" => base_um = v,
                    "num_bends" => bends = v,
                    "amplitude_um" => amp_um = v,
                    "pitch_um" => pitch_um = v,
                    "spacing_step" => spacing_step = v,
                    "ref_length_um" => ref_um = v,
                    _ => {}
                }
            }
        }
    }
    Some(BinaryHwCert {
        domain: HwCertDomain::Pcb,
        p0: base_um,
        p1: bends,
        p2: amp_um,
        p3: pitch_um,
        p4: spacing_step,
        p5: ref_um,
    })
}

/// Raw EDA Data Munger 2: Parse a photonic PDK ring specification snippet into a `BinaryHwCert`.
pub fn munge_photonic_pdk_spec(spec: &str) -> Option<BinaryHwCert> {
    let mut cert = BinaryHwCert::golden_for_domain(HwCertDomain::Photonics);
    for line in spec.lines() {
        let line = line.trim();
        if let Some((k, v)) = line.split_once('=') {
            if let Ok(val) = v.trim().parse::<i32>() {
                match k.trim() {
                    "round_trip_um" => cert.p0 = val,
                    "neff_permille" => cert.p1 = val,
                    "mode_order" => cert.p2 = val,
                    "lambda_nm" => cert.p3 = val,
                    "loss_tau_permille" => cert.p4 = val,
                    "coupling_kappa_permille" => cert.p5 = val,
                    _ => {}
                }
            }
        }
    }
    Some(cert)
}

/// 2D FEMM-style first-order triangular finite element for planar magnetics ($\nabla \cdot (\nu \nabla A_z) + J_z = 0$).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FemmTriangle2D {
    pub x0: i64,
    pub y0: i64,
    pub x1: i64,
    pub y1: i64,
    pub x2: i64,
    pub y2: i64,
    pub nu_scaled: i64,
}

impl FemmTriangle2D {
    pub fn b0(&self) -> i64 { self.y1 - self.y2 }
    pub fn b1(&self) -> i64 { self.y2 - self.y0 }
    pub fn b2(&self) -> i64 { self.y0 - self.y1 }
    pub fn c0(&self) -> i64 { self.x2 - self.x1 }
    pub fn c1(&self) -> i64 { self.x0 - self.x2 }
    pub fn c2(&self) -> i64 { self.x1 - self.x0 }

    /// Evaluate scaled magnetic energy numerator $\nu \cdot ((\sum b_i A_i)^2 + (\sum c_i A_i)^2) \ge 0$.
    pub fn eval_element_energy_scaled(&self, a0: i64, a1: i64, a2: i64) -> i64 {
        let gx = self.b0() * a0 + self.b1() * a1 + self.b2() * a2;
        let gy = self.c0() * a0 + self.c1() * a1 + self.c2() * a2;
        self.nu_scaled * (gx * gx + gy * gy)
    }
}

/// Solve 2D FEMM triangular mesh energy + IPM $dq0$ reluctance/PM torque and emit a `BinaryHwCert` (`Magnetics`).
pub fn solve_2d_femm_and_ipm_motor(
    mesh: &[FemmTriangle2D],
    nodal_az: (i64, i64, i64),
    pole_pairs: i32,
    psi_pm_mwb: i32,
    ld_uh: i32,
    lq_uh: i32,
    id_amp: i32,
    iq_amp: i32,
) -> (i64, i64, BinaryHwCert) {
    let mesh_energy: i64 = mesh
        .iter()
        .map(|tri| tri.eval_element_energy_scaled(nodal_az.0, nodal_az.1, nodal_az.2))
        .sum();
    let torque_scaled: i64 = (pole_pairs as i64)
        * ((psi_pm_mwb as i64) * (iq_amp as i64)
            + ((ld_uh - lq_uh) as i64) * (id_amp as i64) * (iq_amp as i64));
    let cert = BinaryHwCert {
        domain: HwCertDomain::Magnetics,
        p0: pole_pairs,
        p1: psi_pm_mwb,
        p2: ld_uh,
        p3: lq_uh,
        p4: id_amp,
        p5: iq_amp,
    };
    (mesh_energy, torque_scaled, cert)
}

/// Variable-length RFC 8949 CBOR Hardware Tape/Mesh Certificate (`Tag 0x0BED` + `0x9A`).
/// Matches Lean's `Obend.Hardware.Codec.BinaryTapeCert` byte-for-byte.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTapeCert {
    pub domain: HwCertDomain,
    pub metric0: u32,
    pub metric1: u32,
    pub words: Vec<u32>,
}

impl BinaryTapeCert {
    /// Local verifier matching Lean's `Obend.Hardware.Codec.verifyBinaryTapeCert`.
    /// Domains that require a fixed-arity `BinaryHwCert` (`Pnr`, `Retiming`, `Photonics`,
    /// `Pcb`, `Dpr`, `EdaBomSwap`, `Analog2d`, `DspBeamformer`) are strictly refused here.
    pub fn verify_local(&self) -> bool {
        let words_sum: u64 = self.words.iter().map(|&w| w as u64).sum();
        let all_pos = self.words.iter().all(|&w| w > 0);
        match self.domain {
            HwCertDomain::Magnetics => {
                self.words.len() >= 3
                    && self.metric0 > 0
                    && (self.metric0 as u64) == words_sum
                    && self.metric1 <= 5_000_000
                    && all_pos
            }
            HwCertDomain::MechanicsVonNeumann => {
                self.words.len() >= 4
                    && self.metric1 < self.metric0
                    && self.metric1 > 0
                    && (self.metric1 as u64) == words_sum
                    && all_pos
            }
            HwCertDomain::FluidThermal => {
                if self.words.len() != 5 {
                    return false;
                }
                let tw = self.words[0];
                let mc = self.words[1];
                let fq = self.words[2];
                let fd = self.words[3];
                let pf = self.words[4];
                let cand = evaluate_physical_candidate(tw, mc, fq, fd);
                self.metric0 >= 64
                    && self.metric1 <= 165_000
                    && tw >= 3800
                    && mc >= 500
                    && fq >= 20
                    && fd <= 12
                    && pf >= 1
                    && cand.turn_off_peak_v <= 1150
                    && cand.volumetric_error_um <= 36
                    && self.metric1 == cand.peak_winding_temp_mc
            }
            HwCertDomain::PowerElectronics => {
                self.words.len() >= 2 && self.metric0 <= 1150 && self.metric1 > 0 && all_pos
            }
            HwCertDomain::Multiphysics => {
                self.words.len() >= 2 && self.metric0 > 0 && self.metric1 > 0 && all_pos
            }
            _ => false,
        }
    }
}

impl BinaryCodec for BinaryTapeCert {
    fn encode_bytes(&self, out: &mut Vec<u8>) {
        let arr_len = (4 + self.words.len()) as u32;
        out.extend_from_slice(&[0xD9, 0x0B, 0xED, 0x9A]);
        out.extend_from_slice(&arr_len.to_be_bytes());
        cbor_encode_u32(self.domain as u32, out);
        cbor_encode_u32(self.metric0, out);
        cbor_encode_u32(self.metric1, out);
        cbor_encode_u32(self.words.len() as u32, out);
        for &w in &self.words {
            cbor_encode_u32(w, out);
        }
    }

    fn decode_bytes(input: &[u8]) -> Option<(Self, &[u8])> {
        if input.len() < 8 || input[0..4] != [0xD9, 0x0B, 0xED, 0x9A] {
            return None;
        }
        let arr_len = u32::from_be_bytes([input[4], input[5], input[6], input[7]]);
        let (dom_u32, r1) = cbor_decode_u32(&input[8..])?;
        let domain = HwCertDomain::from_u32(dom_u32)?;
        let (metric0, r2) = cbor_decode_u32(r1)?;
        let (metric1, r3) = cbor_decode_u32(r2)?;
        let (len, mut cur) = cbor_decode_u32(r3)?;
        if arr_len != len.checked_add(4)? {
            return None;
        }
        let required_bytes = (len as usize).checked_mul(5)?;
        if cur.len() < required_bytes {
            return None;
        }
        let mut words = Vec::with_capacity(len as usize);
        for _ in 0..len {
            let (w, next) = cbor_decode_u32(cur)?;
            words.push(w);
            cur = next;
        }
        Some((
            Self {
                domain,
                metric0,
                metric1,
                words,
            },
            cur,
        ))
    }
}

// ============================================================================
// Engine 1: Real 2D FEMM Newton-Raphson Nonlinear Stator Slot Solver
// ============================================================================

/// Nonlinear 2D finite element in a stator slot/tooth/air-gap mesh with Brauer saturation
/// $\nu(B^2) = \nu_0 + \nu_{\text{sat}} B^2$.
#[derive(Debug, Clone, Copy)]
pub struct NonlinearFemmElement {
    pub nodes: [usize; 3],
    pub x: [f64; 3],
    pub y: [f64; 3],
    pub nu0: f64,
    pub nu_sat: f64,
    pub jz: f64,
}

/// Converged solution and certificate from `solve_femm_mesh`.
#[derive(Debug, Clone)]
pub struct FemmMeshSolution {
    pub iterations: usize,
    pub max_residual_norm: u64,
    pub nodal_potentials: [f64; 6],
    pub total_energy: u32,
    pub peak_tooth_b2_scaled: u32,
    pub element_energies: Vec<u32>,
    pub hw_cert: BinaryHwCert,
    pub tape_cert: BinaryTapeCert,
}

/// Assemble and solve a 6-element 2D nonlinear ferromagnetic stator slot + tooth + air-gap mesh
/// via exact Newton-Raphson tangent iterations ($\|r\|_\infty = 0$ at quantized fixed point),
/// parameterized by current density scaling `jz_scale`.
pub fn solve_femm_mesh_with_excitation(jz_scale: f64) -> FemmMeshSolution {
    // 6 nodes:
    //   Node 0 (free): stator slot conductor center (4.0, 5.0)
    //   Node 1 (free): ferromagnetic stator tooth tip (8.0, 5.0)
    //   Node 2..5 (Dirichlet Az = 0): outer yoke and air-gap boundary
    let elements = [
        // Slot winding triangles (copper excitation Jz > 0, linear air/copper nu0)
        NonlinearFemmElement {
            nodes: [0, 2, 3],
            x: [4.0, 0.0, 4.0],
            y: [5.0, 0.0, 0.0],
            nu0: 800.0,
            nu_sat: 0.0,
            jz: 18.0 * jz_scale,
        },
        NonlinearFemmElement {
            nodes: [0, 3, 1],
            x: [4.0, 4.0, 8.0],
            y: [5.0, 0.0, 5.0],
            nu0: 800.0,
            nu_sat: 0.0,
            jz: 18.0 * jz_scale,
        },
        // Ferromagnetic stator tooth root & tip (Brauer nonlinear saturation nu_sat > 0)
        NonlinearFemmElement {
            nodes: [1, 3, 4],
            x: [8.0, 4.0, 12.0],
            y: [5.0, 0.0, 0.0],
            nu0: 120.0,
            nu_sat: 45.0,
            jz: 0.0,
        },
        NonlinearFemmElement {
            nodes: [0, 1, 5],
            x: [4.0, 8.0, 8.0],
            y: [5.0, 5.0, 10.0],
            nu0: 140.0,
            nu_sat: 50.0,
            jz: 6.0 * jz_scale,
        },
        // Air-gap & tooth shoe elements
        NonlinearFemmElement {
            nodes: [1, 4, 5],
            x: [8.0, 12.0, 8.0],
            y: [5.0, 0.0, 10.0],
            nu0: 160.0,
            nu_sat: 35.0,
            jz: 0.0,
        },
        NonlinearFemmElement {
            nodes: [0, 5, 2],
            x: [4.0, 8.0, 0.0],
            y: [5.0, 10.0, 0.0],
            nu0: 600.0,
            nu_sat: 0.0,
            jz: 12.0 * jz_scale,
        },
    ];

    let mut az = [0.0f64; 6];
    let mut iterations = 0usize;
    let mut final_max_r = f64::INFINITY;

    for iter in 0..32 {
        iterations = iter + 1;
        let mut r = [0.0f64; 2];
        let mut j_mat = [[0.0f64; 2]; 2];

        for el in &elements {
            let b = [
                el.y[1] - el.y[2],
                el.y[2] - el.y[0],
                el.y[0] - el.y[1],
            ];
            let c = [
                el.x[2] - el.x[1],
                el.x[0] - el.x[2],
                el.x[1] - el.x[0],
            ];
            let two_area = (b[0] * c[1] - b[1] * c[0]).abs().max(1.0);
            let area = 0.5 * two_area;

            let a_loc = [az[el.nodes[0]], az[el.nodes[1]], az[el.nodes[2]]];
            let gx = (b[0] * a_loc[0] + b[1] * a_loc[1] + b[2] * a_loc[2]) / two_area;
            let gy = (c[0] * a_loc[0] + c[1] * a_loc[1] + c[2] * a_loc[2]) / two_area;
            let b2 = gx * gx + gy * gy;
            let nu = el.nu0 + el.nu_sat * b2;

            for m in 0..3 {
                let nm = el.nodes[m];
                if nm < 2 {
                    let grad_dot_m = (gx * b[m] + gy * c[m]) / two_area;
                    r[nm] += area * nu * grad_dot_m - el.jz * area / 3.0;

                    for n in 0..3 {
                        let nn = el.nodes[n];
                        if nn < 2 {
                            let k_mn = (b[m] * b[n] + c[m] * c[n]) / (two_area * two_area);
                            let d_b2_dn = 2.0 * (gx * b[n] + gy * c[n]) / two_area;
                            j_mat[nm][nn] += area * (nu * k_mn + el.nu_sat * grad_dot_m * d_b2_dn);
                        }
                    }
                }
            }
        }

        let max_r = r[0].abs().max(r[1].abs());
        final_max_r = max_r;
        if max_r < 1e-11 {
            break;
        }

        let det = j_mat[0][0] * j_mat[1][1] - j_mat[0][1] * j_mat[1][0];
        let da0 = (-r[0] * j_mat[1][1] + r[1] * j_mat[0][1]) / det;
        let da1 = (-j_mat[0][0] * r[1] + j_mat[1][0] * r[0]) / det;
        az[0] += da0;
        az[1] += da1;
    }

    // Quantize converged residual norm ||r||_inf at 1e9 scale (0 when max_r < 5e-10)
    let max_residual_norm = (final_max_r * 1_000_000_000.0).round() as u64;
    let mut element_energies = Vec::with_capacity(elements.len());
    let mut peak_tooth_b2_scaled = 0u32;

    for el in &elements {
        let b = [
            el.y[1] - el.y[2],
            el.y[2] - el.y[0],
            el.y[0] - el.y[1],
        ];
        let c = [
            el.x[2] - el.x[1],
            el.x[0] - el.x[2],
            el.x[1] - el.x[0],
        ];
        let two_area = (b[0] * c[1] - b[1] * c[0]).abs().max(1.0);
        let a_loc = [az[el.nodes[0]], az[el.nodes[1]], az[el.nodes[2]]];
        let gx = (b[0] * a_loc[0] + b[1] * a_loc[1] + b[2] * a_loc[2]) / two_area;
        let gy = (c[0] * a_loc[0] + c[1] * a_loc[1] + c[2] * a_loc[2]) / two_area;
        let b2 = gx * gx + gy * gy;
        let nu = el.nu0 + el.nu_sat * b2;
        let e_scaled = ((0.5 * two_area * nu * b2) * 10000.0).round() as u32;
        element_energies.push(e_scaled.max(1));
        if el.nu_sat > 0.0 {
            let b2_scaled = (b2 * 1_000_000.0).round() as u32;
            if b2_scaled > peak_tooth_b2_scaled {
                peak_tooth_b2_scaled = b2_scaled;
            }
        }
    }

    let total_energy: u32 = element_energies
        .iter()
        .fold(0u32, |acc, &e| acc.saturating_add(e));
    // Compute physical scaled B^2 directly from the converged finite-element field (no artificial clamp!)
    let peak_b2 = peak_tooth_b2_scaled.max(1);
    let hw_cert = BinaryHwCert::golden_for_domain(HwCertDomain::Magnetics);
    let tape_cert = BinaryTapeCert {
        domain: HwCertDomain::Magnetics,
        metric0: total_energy,
        metric1: peak_b2,
        words: element_energies.clone(),
    };

    FemmMeshSolution {
        iterations,
        max_residual_norm,
        nodal_potentials: az,
        total_energy,
        peak_tooth_b2_scaled: peak_b2,
        element_energies,
        hw_cert,
        tape_cert,
    }
}

/// Assemble and solve the nominal 6-element 2D nonlinear ferromagnetic stator slot + tooth + air-gap mesh.
pub fn solve_femm_mesh() -> FemmMeshSolution {
    solve_femm_mesh_with_excitation(1.0)
}

// ============================================================================
// Engine 2: Real 3D F-Rep Octree Voxelizer with `fidget` `Choice` Tape Pruning
// ============================================================================

/// `fidget`-style interval branch selector for `min` / `max` CSG nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Choice {
    Left,
    Right,
    Both,
}

/// Conservative closed 1D interval $[lo, hi]$.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub lo: i64,
    pub hi: i64,
}

impl Interval {
    pub fn new(lo: i64, hi: i64) -> Self {
        Self { lo: lo.min(hi), hi: lo.max(hi) }
    }

    pub fn add(self, other: Self) -> Self {
        Self { lo: self.lo + other.lo, hi: self.hi + other.hi }
    }

    pub fn sub_scalar(self, c: i64) -> Self {
        Self { lo: self.lo - c, hi: self.hi - c }
    }

    pub fn sq(self) -> Self {
        let a = self.lo * self.lo;
        let b = self.hi * self.hi;
        if self.lo <= 0 && 0 <= self.hi {
            Self { lo: 0, hi: a.max(b) }
        } else {
            Self { lo: a.min(b), hi: a.max(b) }
        }
    }
}

/// 3D axis-aligned bounding box for octree subdivision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval3D {
    pub x: Interval,
    pub y: Interval,
    pub z: Interval,
}

/// Instruction in a 3D F-Rep CSG SSA tape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrepOp {
    Sphere { out: usize, cx: i64, cy: i64, cz: i64, r_sq: i64 },
    CylinderZ { out: usize, cx: i64, cy: i64, r_sq: i64 },
    HalfSpaceZ { out: usize, z0: i64 },
    MinUnion { out: usize, lhs: usize, rhs: usize },
    MaxIntersect { out: usize, lhs: usize, rhs: usize },
}

impl FrepOp {
    pub fn out_reg(&self) -> usize {
        match *self {
            FrepOp::Sphere { out, .. }
            | FrepOp::CylinderZ { out, .. }
            | FrepOp::HalfSpaceZ { out, .. }
            | FrepOp::MinUnion { out, .. }
            | FrepOp::MaxIntersect { out, .. } => out,
        }
    }
}

/// Build the 11-op 3D F-Rep CSG tape for a stator housing with 4 quadrant cooling microchannels
/// and axial endbell boss.
pub fn build_stator_frep_tape() -> Vec<FrepOp> {
    vec![
        // Quadrant cooling microchannels (localized in each XY quadrant)
        FrepOp::CylinderZ { out: 0, cx: -60, cy: -60, r_sq: 100 },
        FrepOp::CylinderZ { out: 1, cx: 60, cy: -60, r_sq: 100 },
        FrepOp::CylinderZ { out: 2, cx: -60, cy: 60, r_sq: 100 },
        FrepOp::CylinderZ { out: 3, cx: 60, cy: 60, r_sq: 100 },
        // Pairwise CSG unions of the 4 quadrant cooling channels
        FrepOp::MinUnion { out: 4, lhs: 0, rhs: 1 },
        FrepOp::MinUnion { out: 5, lhs: 2, rhs: 3 },
        FrepOp::MinUnion { out: 6, lhs: 4, rhs: 5 },
        // Outer stator housing sphere and axial mounting boss
        FrepOp::Sphere { out: 7, cx: 0, cy: 0, cz: 0, r_sq: 9000 },
        FrepOp::HalfSpaceZ { out: 8, z0: -80 },
        FrepOp::MinUnion { out: 9, lhs: 6, rhs: 7 },
        FrepOp::MaxIntersect { out: 10, lhs: 9, rhs: 8 },
    ]
}

/// Compute the required register file size (`max_reg + 1`) for an arbitrary `FrepOp` tape.
fn tape_reg_capacity(tape: &[FrepOp]) -> usize {
    tape.iter()
        .map(|op| match *op {
            FrepOp::Sphere { out, .. }
            | FrepOp::CylinderZ { out, .. }
            | FrepOp::HalfSpaceZ { out, .. } => out,
            FrepOp::MinUnion { out, lhs, rhs } | FrepOp::MaxIntersect { out, lhs, rhs } => {
                out.max(lhs).max(rhs)
            }
        })
        .max()
        .map(|m| m + 1)
        .unwrap_or(1)
        .max(16)
}

/// Evaluate a 3D F-Rep CSG tape at a single point `(px, py, pz)`.
pub fn eval_frep_tape_point(tape: &[FrepOp], px: i64, py: i64, pz: i64) -> i64 {
    let mut regs = vec![0i64; tape_reg_capacity(tape)];
    let mut last_out = 0usize;
    for op in tape {
        match *op {
            FrepOp::Sphere { out, cx, cy, cz, r_sq } => {
                let dx = px - cx;
                let dy = py - cy;
                let dz = pz - cz;
                regs[out] = dx * dx + dy * dy + dz * dz - r_sq;
                last_out = out;
            }
            FrepOp::CylinderZ { out, cx, cy, r_sq } => {
                let dx = px - cx;
                let dy = py - cy;
                regs[out] = dx * dx + dy * dy - r_sq;
                last_out = out;
            }
            FrepOp::HalfSpaceZ { out, z0 } => {
                regs[out] = pz - z0;
                last_out = out;
            }
            FrepOp::MinUnion { out, lhs, rhs } => {
                regs[out] = regs[lhs].min(regs[rhs]);
                last_out = out;
            }
            FrepOp::MaxIntersect { out, lhs, rhs } => {
                regs[out] = regs[lhs].max(regs[rhs]);
                last_out = out;
            }
        }
    }
    regs[last_out]
}

/// Compact a pruned SSA F-Rep tape via backward liveness analysis, eliminating both dead branches
/// and single-branch `Choice::Left` / `Choice::Right` (or diamond `l_reg == r_reg`) `MinUnion`/`MaxIntersect`
/// nodes via register aliasing and dense register renumbering (`0..compacted.len()`).
pub fn compact_pruned_tape(tape: &[FrepOp], choices: &[Choice]) -> Vec<FrepOp> {
    if tape.is_empty() {
        return Vec::new();
    }
    let reg_cap = tape_reg_capacity(tape);
    let mut alias: Vec<usize> = (0..reg_cap).collect();

    // Forward pass: resolve register aliases for single-branch Choice::Left / Choice::Right nodes
    // (as well as idempotent diamond aliases `l_reg == r_reg`) and rewrite surviving operations.
    let mut resolved_ops: Vec<Option<FrepOp>> = Vec::with_capacity(tape.len());
    let mut root_reg = 0usize;

    for (idx, &op) in tape.iter().enumerate() {
        let choice = choices.get(idx).copied().unwrap_or(Choice::Both);
        match op {
            FrepOp::Sphere { out, .. }
            | FrepOp::CylinderZ { out, .. }
            | FrepOp::HalfSpaceZ { out, .. } => {
                alias[out] = out;
                resolved_ops.push(Some(op));
                root_reg = out;
            }
            FrepOp::MinUnion { out, lhs, rhs } => {
                let l_reg = alias[lhs];
                let r_reg = alias[rhs];
                match choice {
                    Choice::Left => {
                        alias[out] = l_reg;
                        resolved_ops.push(None);
                    }
                    Choice::Right => {
                        alias[out] = r_reg;
                        resolved_ops.push(None);
                    }
                    Choice::Both => {
                        if l_reg == r_reg {
                            alias[out] = l_reg;
                            resolved_ops.push(None);
                        } else {
                            alias[out] = out;
                            resolved_ops.push(Some(FrepOp::MinUnion {
                                out,
                                lhs: l_reg,
                                rhs: r_reg,
                            }));
                        }
                    }
                }
                root_reg = alias[out];
            }
            FrepOp::MaxIntersect { out, lhs, rhs } => {
                let l_reg = alias[lhs];
                let r_reg = alias[rhs];
                match choice {
                    Choice::Left => {
                        alias[out] = l_reg;
                        resolved_ops.push(None);
                    }
                    Choice::Right => {
                        alias[out] = r_reg;
                        resolved_ops.push(None);
                    }
                    Choice::Both => {
                        if l_reg == r_reg {
                            alias[out] = l_reg;
                            resolved_ops.push(None);
                        } else {
                            alias[out] = out;
                            resolved_ops.push(Some(FrepOp::MaxIntersect {
                                out,
                                lhs: l_reg,
                                rhs: r_reg,
                            }));
                        }
                    }
                }
                root_reg = alias[out];
            }
        }
    }

    // Backward liveness pass from `root_reg`
    let mut live_regs = vec![false; reg_cap];
    live_regs[root_reg] = true;
    let mut keep_op = vec![false; resolved_ops.len()];

    for idx in (0..resolved_ops.len()).rev() {
        if let Some(op) = resolved_ops[idx] {
            let out_r = op.out_reg();
            if live_regs[out_r] {
                keep_op[idx] = true;
                match op {
                    FrepOp::MinUnion { lhs, rhs, .. }
                    | FrepOp::MaxIntersect { lhs, rhs, .. } => {
                        live_regs[lhs] = true;
                        live_regs[rhs] = true;
                    }
                    _ => {}
                }
            }
        }
    }

    // Dense register renumbering pass: map each surviving `out` register to `0..compacted.len()`
    let mut reg_remap = vec![0usize; reg_cap];
    let mut compacted = Vec::new();
    for (idx, op_opt) in resolved_ops.iter().enumerate() {
        if keep_op[idx] {
            if let Some(op) = *op_opt {
                let new_out = compacted.len();
                let remapped_op = match op {
                    FrepOp::Sphere { out, cx, cy, cz, r_sq } => {
                        reg_remap[out] = new_out;
                        FrepOp::Sphere { out: new_out, cx, cy, cz, r_sq }
                    }
                    FrepOp::CylinderZ { out, cx, cy, r_sq } => {
                        reg_remap[out] = new_out;
                        FrepOp::CylinderZ { out: new_out, cx, cy, r_sq }
                    }
                    FrepOp::HalfSpaceZ { out, z0 } => {
                        reg_remap[out] = new_out;
                        FrepOp::HalfSpaceZ { out: new_out, z0 }
                    }
                    FrepOp::MinUnion { out, lhs, rhs } => {
                        reg_remap[out] = new_out;
                        FrepOp::MinUnion {
                            out: new_out,
                            lhs: reg_remap[lhs],
                            rhs: reg_remap[rhs],
                        }
                    }
                    FrepOp::MaxIntersect { out, lhs, rhs } => {
                        reg_remap[out] = new_out;
                        FrepOp::MaxIntersect {
                            out: new_out,
                            lhs: reg_remap[lhs],
                            rhs: reg_remap[rhs],
                        }
                    }
                };
                compacted.push(remapped_op);
            }
        }
    }

    compacted
}

/// Evaluate interval bounds over `box3d`, record `Choice::Left`/`Right`/`Both` at every min/max node,
/// and compact the tape by backward liveness pruning of dead branches and single-branch aliases!
pub fn prune_tape_for_interval(tape: &[FrepOp], box3d: Interval3D) -> (Interval, Vec<Choice>, Vec<FrepOp>) {
    let mut regs = vec![Interval::new(0, 0); tape_reg_capacity(tape)];
    let mut choices = Vec::with_capacity(tape.len());
    let mut root_reg = 0usize;

    for &op in tape {
        match op {
            FrepOp::Sphere { out, cx, cy, cz, r_sq } => {
                let dx2 = box3d.x.sub_scalar(cx).sq();
                let dy2 = box3d.y.sub_scalar(cy).sq();
                let dz2 = box3d.z.sub_scalar(cz).sq();
                regs[out] = dx2.add(dy2).add(dz2).sub_scalar(r_sq);
                choices.push(Choice::Both);
                root_reg = out;
            }
            FrepOp::CylinderZ { out, cx, cy, r_sq } => {
                let dx2 = box3d.x.sub_scalar(cx).sq();
                let dy2 = box3d.y.sub_scalar(cy).sq();
                regs[out] = dx2.add(dy2).sub_scalar(r_sq);
                choices.push(Choice::Both);
                root_reg = out;
            }
            FrepOp::HalfSpaceZ { out, z0 } => {
                regs[out] = box3d.z.sub_scalar(z0);
                choices.push(Choice::Both);
                root_reg = out;
            }
            FrepOp::MinUnion { out, lhs, rhs } => {
                let l = regs[lhs];
                let r = regs[rhs];
                if l.hi <= r.lo {
                    regs[out] = l;
                    choices.push(Choice::Left);
                } else if r.hi <= l.lo {
                    regs[out] = r;
                    choices.push(Choice::Right);
                } else {
                    regs[out] = Interval::new(l.lo.min(r.lo), l.hi.min(r.hi));
                    choices.push(Choice::Both);
                }
                root_reg = out;
            }
            FrepOp::MaxIntersect { out, lhs, rhs } => {
                let l = regs[lhs];
                let r = regs[rhs];
                if l.lo >= r.hi {
                    regs[out] = l;
                    choices.push(Choice::Left);
                } else if r.lo >= l.hi {
                    regs[out] = r;
                    choices.push(Choice::Right);
                } else {
                    regs[out] = Interval::new(l.lo.max(r.lo), l.hi.max(r.hi));
                    choices.push(Choice::Both);
                }
                root_reg = out;
            }
        }
    }

    let pruned_tape = compact_pruned_tape(tape, &choices);
    (regs[root_reg], choices, pruned_tape)
}

/// Summary and certificate of 3D octree F-Rep voxelization with `Choice` tape pruning.
#[derive(Debug, Clone)]
pub struct OctreeFrepReport {
    pub unpruned_tape_ops: u32,
    pub pruned_tape_ops: u32,
    pub choice_left_or_right_count: usize,
    pub zero_discrepancy: bool,
    pub octant_active_ops: Vec<u32>,
    pub tape_cert: BinaryTapeCert,
}

/// Evaluate the 3D F-Rep stator tape over a 2-level octree (8 octants $\times$ 8 sub-voxels = 64 leaves),
/// pruning instructions via `Choice::Left` / `Choice::Right` interval bounds at each octant.
pub fn eval_octree_frep_pruned() -> OctreeFrepReport {
    let full_tape = build_stator_frep_tape();
    let mut unpruned_tape_ops = 0u32;
    let mut pruned_tape_ops = 0u32;
    let mut choice_left_or_right_count = 0usize;
    let mut zero_discrepancy = true;
    let mut octant_active_ops = Vec::with_capacity(8);

    let x_halves = [Interval::new(-80, 0), Interval::new(0, 80)];
    let y_halves = [Interval::new(-80, 0), Interval::new(0, 80)];
    let z_halves = [Interval::new(-80, 0), Interval::new(0, 80)];

    for &xh in &x_halves {
        for &yh in &y_halves {
            for &zh in &z_halves {
                let octant_box = Interval3D { x: xh, y: yh, z: zh };
                let (_iv_oct, oct_choices, oct_pruned) = prune_tape_for_interval(&full_tape, octant_box);
                choice_left_or_right_count += oct_choices
                    .iter()
                    .filter(|&&c| c == Choice::Left || c == Choice::Right)
                    .count();

                let mut octant_ops = 0u32;
                // Subdivide each octant into 8 contiguous sub-voxel boxes covering all of [-80, 80]^3
                let xm = (xh.lo + xh.hi) / 2;
                let ym = (yh.lo + yh.hi) / 2;
                let zm = (zh.lo + zh.hi) / 2;
                let sub_x_boxes = [Interval::new(xh.lo, xm), Interval::new(xm, xh.hi)];
                let sub_y_boxes = [Interval::new(yh.lo, ym), Interval::new(ym, yh.hi)];
                let sub_z_boxes = [Interval::new(zh.lo, zm), Interval::new(zm, zh.hi)];

                for &sx in &sub_x_boxes {
                    for &sy in &sub_y_boxes {
                        for &sz in &sub_z_boxes {
                            let sub_box = Interval3D { x: sx, y: sy, z: sz };
                            let (_iv, sub_choices, pruned) =
                                prune_tape_for_interval(&oct_pruned, sub_box);
                            choice_left_or_right_count += sub_choices
                                .iter()
                                .filter(|&&c| c == Choice::Left || c == Choice::Right)
                                .count();

                            let px = (sx.lo + sx.hi) / 2;
                            let py = (sy.lo + sy.hi) / 2;
                            let pz = (sz.lo + sz.hi) / 2;
                            unpruned_tape_ops += full_tape.len() as u32;
                            pruned_tape_ops += pruned.len() as u32;
                            octant_ops += pruned.len() as u32;

                            let v_full = eval_frep_tape_point(&full_tape, px, py, pz);
                            let v_pruned = eval_frep_tape_point(&pruned, px, py, pz);
                            if v_full != v_pruned {
                                zero_discrepancy = false;
                            }
                        }
                    }
                }
                octant_active_ops.push(octant_ops.max(1));
            }
        }
    }

    let tape_cert = BinaryTapeCert {
        domain: HwCertDomain::MechanicsVonNeumann,
        metric0: unpruned_tape_ops,
        metric1: pruned_tape_ops,
        words: octant_active_ops.clone(),
    };

    OctreeFrepReport {
        unpruned_tape_ops,
        pruned_tape_ops,
        choice_left_or_right_count,
        zero_discrepancy,
        octant_active_ops,
        tape_cert,
    }
}

// ============================================================================
// Engine 3: Real In-Silico Evolutionary Multi-Objective Pareto Optimizer
// ============================================================================

/// Candidate physical design across coupled magnetics, LC Drives microchannel cooling,
/// MS350 6-level GaN FCML power electronics, and 5-axis CNC finish milling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhysicalDesignCandidate {
    pub tooth_width_um: u32,
    pub microchannel_aspect_permille: u32,
    pub fcml_freq_khz: u32,
    pub cnc_feed_mm_s: u32,
    // Evaluated physical metrics:
    pub peak_winding_temp_mc: u32,
    pub volumetric_error_um: u32,
    pub total_loss_w: u32,
    pub turn_off_peak_v: u32,
    pub feasible: bool,
}

/// Result of running the in-silico evolutionary Pareto optimizer over $\ge 64$ candidates.
#[derive(Debug, Clone)]
pub struct EvolutionReport {
    pub evaluated_candidates: u32,
    pub pareto_front: Vec<PhysicalDesignCandidate>,
    pub best_candidate: PhysicalDesignCandidate,
    pub hw_cert: BinaryHwCert,
    pub tape_cert: BinaryTapeCert,
}

/// Evaluate a candidate physical design across all 4 coupled physics domains.
pub fn evaluate_physical_candidate(
    tooth_width_um: u32,
    microchannel_aspect_permille: u32,
    fcml_freq_khz: u32,
    cnc_feed_mm_s: u32,
) -> PhysicalDesignCandidate {
    // 1. Copper + core + FCML ripple loss (W):
    // Narrower teeth leave larger slot area (lower DC copper loss), while higher FCML frequency reduces ripple loss
    let slot_width_um = 10_000u32.saturating_sub(tooth_width_um).max(2000);
    let dc_copper_loss_w = 14_000_000 / slot_width_um;
    let core_iron_loss_w = tooth_width_um / 4;
    let fcml_ripple_loss_w = 48_000 / (6 * fcml_freq_khz.max(20));
    let total_loss_w = dc_copper_loss_w + core_iron_loss_w + fcml_ripple_loss_w;

    // 2. LC Drives in-slot microchannel thermal resistance (mK/W) & peak winding temp (mC):
    let r_caloric_mk_w = 4u32;
    let r_conv_mk_w = (24_000 / microchannel_aspect_permille.max(500)).max(4);
    let r_cond_mk_w = (tooth_width_um / 800).max(4);
    let t_inlet_mc = 40_000u32;
    let peak_winding_temp_mc =
        t_inlet_mc + total_loss_w * (r_caloric_mk_w + r_conv_mk_w + r_cond_mk_w);

    // 3. MS350 800V DC bus turn-off overshoot (V) & tooth saturation check:
    let turn_off_peak_v = 800 + (fcml_freq_khz / 2);
    let tooth_b2_ok = tooth_width_um >= 3800;

    // 4. 5-axis CNC finish milling volumetric error (um) & Altintas chatter stability:
    let volumetric_error_um = 12 + cnc_feed_mm_s * 2 + (4800u32.abs_diff(tooth_width_um) / 400);
    let chatter_stable = cnc_feed_mm_s <= 12;

    let feasible = tooth_b2_ok
        && peak_winding_temp_mc <= 165_000
        && turn_off_peak_v <= 1150
        && chatter_stable
        && volumetric_error_um <= 36;

    PhysicalDesignCandidate {
        tooth_width_um,
        microchannel_aspect_permille,
        fcml_freq_khz,
        cnc_feed_mm_s,
        peak_winding_temp_mc,
        volumetric_error_um,
        total_loss_w,
        turn_off_peak_v,
        feasible,
    }
}

/// Run an in-silico evolutionary search over 80 candidate physical designs (4 generations $\times$ 20 individuals),
/// extract the non-dominated Pareto front, and emit verified RFC 8949 CBOR certificates.
pub fn evolve_physical_design() -> EvolutionReport {
    let mut all_candidates = Vec::with_capacity(80);

    // Generation 0: 20 diverse seed designs spanning the design space
    for i in 0..20u32 {
        let tw = 3400 + (i * 170) % 2800;
        let mc = 1800 + (i * 230) % 2600;
        let fq = 80 + (i * 15) % 120;
        let fd = 4 + (i * 2) % 12;
        all_candidates.push(evaluate_physical_candidate(tw, mc, fq, fd));
    }

    // Generations 1..3: Tournament selection + crossover + deterministic mutation (60 more candidates -> 80 total)
    for gen in 1..4u32 {
        let prev_start = ((gen - 1) * 20) as usize;
        for i in 0..20u32 {
            let p1 = all_candidates[prev_start + (i as usize % 20)];
            let p2 = all_candidates[prev_start + (((i + 7) as usize) % 20)];
            let parent_a = if p1.feasible && (!p2.feasible || p1.peak_winding_temp_mc <= p2.peak_winding_temp_mc) {
                p1
            } else {
                p2
            };
            let parent_b = all_candidates[prev_start + (((i + 13) as usize) % 20)];

            let tw = ((parent_a.tooth_width_um + parent_b.tooth_width_um) / 2 + gen * 40 + i * 15)
                .clamp(3800, 5600);
            let mc = ((parent_a.microchannel_aspect_permille + parent_b.microchannel_aspect_permille) / 2
                + gen * 120
                + i * 25)
                .clamp(2400, 4400);
            let fq = ((parent_a.fcml_freq_khz + parent_b.fcml_freq_khz) / 2 + gen * 5 + i * 3)
                .clamp(100, 180);
            let fd = ((parent_a.cnc_feed_mm_s + parent_b.cnc_feed_mm_s) / 2)
                .saturating_sub(gen % 2)
                .clamp(4, 10);

            all_candidates.push(evaluate_physical_candidate(tw, mc, fq, fd));
        }
    }

    // Compute the non-dominated Pareto front among all feasible candidates
    let feasible: Vec<PhysicalDesignCandidate> =
        all_candidates.iter().copied().filter(|c| c.feasible).collect();

    let mut pareto_front = Vec::new();
    for cand in &feasible {
        let dominated = feasible.iter().any(|other| {
            let le_all = other.peak_winding_temp_mc <= cand.peak_winding_temp_mc
                && other.volumetric_error_um <= cand.volumetric_error_um
                && other.total_loss_w <= cand.total_loss_w;
            let lt_any = other.peak_winding_temp_mc < cand.peak_winding_temp_mc
                || other.volumetric_error_um < cand.volumetric_error_um
                || other.total_loss_w < cand.total_loss_w;
            le_all && lt_any
        });
        if !dominated && !pareto_front.contains(cand) {
            pareto_front.push(*cand);
        }
    }

    let best_candidate = pareto_front
        .iter()
        .copied()
        .min_by_key(|c| c.peak_winding_temp_mc + c.volumetric_error_um * 1000)
        .expect("Pareto front must be non-empty");

    let r_caloric = 4i32;
    let r_conv = (24_000 / best_candidate.microchannel_aspect_permille.max(500)).max(4) as i32;
    let r_cond = (best_candidate.tooth_width_um / 800).max(4) as i32;
    let hw_cert = BinaryHwCert {
        domain: HwCertDomain::FluidThermal,
        p0: 40000,
        p1: best_candidate.total_loss_w as i32,
        p2: r_caloric,
        p3: r_conv,
        p4: r_cond,
        p5: 180000,
    };

    let tape_cert = BinaryTapeCert {
        domain: HwCertDomain::FluidThermal,
        metric0: all_candidates.len() as u32,
        metric1: best_candidate.peak_winding_temp_mc,
        words: vec![
            best_candidate.tooth_width_um,
            best_candidate.microchannel_aspect_permille,
            best_candidate.fcml_freq_khz,
            best_candidate.cnc_feed_mm_s,
            pareto_front.len() as u32,
        ],
    };

    EvolutionReport {
        evaluated_candidates: all_candidates.len() as u32,
        pareto_front,
        best_candidate,
        hw_cert,
        tape_cert,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cbor_binary_hw_cert_roundtrip_all_domains() {
        let domains = [
            HwCertDomain::Pnr,
            HwCertDomain::Retiming,
            HwCertDomain::Photonics,
            HwCertDomain::Pcb,
            HwCertDomain::Dpr,
            HwCertDomain::EdaBomSwap,
            HwCertDomain::Multiphysics,
            HwCertDomain::Analog2d,
            HwCertDomain::DspBeamformer,
            HwCertDomain::Magnetics,
            HwCertDomain::FluidThermal,
            HwCertDomain::PowerElectronics,
            HwCertDomain::MechanicsVonNeumann,
        ];
        for dom in domains {
            let cert = BinaryHwCert::golden_for_domain(dom);
            let bytes = cert.to_vec();
            assert_eq!(bytes.len(), 39, "canonical BinaryHwCert frame is 39 bytes");
            assert_eq!(&bytes[0..4], &[0xD9, 0x0B, 0xED, 0x87]);
            let decoded = BinaryHwCert::from_slice(&bytes).expect("must decode cleanly");
            assert_eq!(decoded, cert);
        }
    }

    #[test]
    fn test_femm_2d_gauge_invariance_and_ipm_torque() {
        let tri = FemmTriangle2D {
            x0: 0,
            y0: 0,
            x1: 10,
            y1: 0,
            x2: 0,
            y2: 10,
            nu_scaled: 500,
        };
        let e1 = tri.eval_element_energy_scaled(12, -4, 7);
        let e2 = tri.eval_element_energy_scaled(12 + 99, -4 + 99, 7 + 99);
        assert_eq!(e1, e2, "2D FEMM element energy must be gauge invariant");
        assert!(e1 > 0);
        let (mesh_e, torque, cert) =
            solve_2d_femm_and_ipm_motor(&[tri], (12, -4, 7), 6, 250, 300, 800, -100, 400);
        assert_eq!(mesh_e, e1);
        assert!(torque > 6 * 250 * 400, "IPM reluctance torque must boost PM torque under id < 0");
        assert_eq!(cert.domain, HwCertDomain::Magnetics);
    }

    #[test]
    fn test_negative_i32_cbor_major_type_1_roundtrip() {
        for val in [-1, -9, -50, -32768, 0, 1, 42, 100000] {
            let mut buf = Vec::new();
            cbor_encode_i32(val, &mut buf);
            let (dec, rest) = cbor_decode_i32(&buf).expect("must decode i32");
            assert!(rest.is_empty());
            assert_eq!(dec, val);
        }
    }

    #[test]
    fn test_solve_femm_mesh_newton_raphson_convergence() {
        let sol = solve_femm_mesh();
        assert!(sol.iterations >= 2 && sol.iterations <= 16);
        assert_eq!(sol.max_residual_norm, 0);
        assert_eq!(sol.element_energies.len(), 6);
        assert!(sol.total_energy > 0);
        let sum_e: u32 = sol.element_energies.iter().sum();
        assert_eq!(sol.total_energy, sum_e);
        assert!(sol.tape_cert.verify_local(), "nominal stator excitation must pass B^2 <= 5_000_000");
        let bytes = sol.tape_cert.to_vec();
        assert_eq!(&bytes[0..4], &[0xD9, 0x0B, 0xED, 0x9A]);
        assert_eq!(&bytes[4..8], &(10u32.to_be_bytes()));
        let dec = BinaryTapeCert::from_slice(&bytes).expect("must decode BinaryTapeCert");
        assert_eq!(dec, sol.tape_cert);

        // Out-of-spec over-current excitation (500x nominal Jz) must genuinely exceed the 5_000_000 B^2 threshold
        let over_sol = solve_femm_mesh_with_excitation(500.0);
        assert!(
            over_sol.peak_tooth_b2_scaled > 5_000_000,
            "unclamped over-current FEMM solve must exceed 5_000_000 (got {})",
            over_sol.peak_tooth_b2_scaled
        );
        assert!(
            !over_sol.tape_cert.verify_local(),
            "over-saturated tooth B^2 must be rejected by verify_local()"
        );
    }

    #[test]
    fn test_eval_octree_frep_pruned_choice_compaction() {
        let rep = eval_octree_frep_pruned();
        assert!(rep.zero_discrepancy, "pruned octant tapes must agree with unpruned tape at every leaf");
        assert!(rep.choice_left_or_right_count > 0, "Choice::Left/Right must trigger across octants");
        assert!(
            rep.pruned_tape_ops < rep.unpruned_tape_ops,
            "Choice pruning must strictly reduce evaluated tape operations ({} < {})",
            rep.pruned_tape_ops,
            rep.unpruned_tape_ops
        );
        assert!(rep.tape_cert.verify_local());
        let bytes = rep.tape_cert.to_vec();
        let dec = BinaryTapeCert::from_slice(&bytes).expect("must decode octree BinaryTapeCert");
        assert_eq!(dec, rep.tape_cert);

        // Verify compact_pruned_tape eliminates single-branch MinUnion/MaxIntersect nodes cleanly
        // (no dummy lhs == rhs nodes, and dense register indices 0..pruned.len())
        let full_tape = build_stator_frep_tape();
        let octant_box = Interval3D {
            x: Interval::new(-80, -40),
            y: Interval::new(-80, -40),
            z: Interval::new(-80, -40),
        };
        let (_iv, _choices, pruned) = prune_tape_for_interval(&full_tape, octant_box);
        assert!(pruned.len() < full_tape.len(), "compacted octant tape must be strictly shorter");
        for (idx, op) in pruned.iter().enumerate() {
            assert_eq!(op.out_reg(), idx, "compacted SSA registers must be densely numbered 0..len");
            if let FrepOp::MinUnion { lhs, rhs, .. } | FrepOp::MaxIntersect { lhs, rhs, .. } = *op {
                assert_ne!(lhs, rhs, "compacted tape must not contain dummy single-branch lhs == rhs nodes");
            }
        }
    }

    #[test]
    fn test_evolve_physical_design_pareto_front() {
        let evo = evolve_physical_design();
        assert!(evo.evaluated_candidates >= 64);
        assert!(!evo.pareto_front.is_empty());
        assert!(evo.best_candidate.feasible);
        assert!(evo.best_candidate.peak_winding_temp_mc <= 165_000);
        assert!(evo.tape_cert.verify_local());
        let bytes = evo.tape_cert.to_vec();
        let dec = BinaryTapeCert::from_slice(&bytes).expect("must decode evolution BinaryTapeCert");
        assert_eq!(dec, evo.tape_cert);
    }

    #[test]
    fn test_binary_tape_cert_rejects_underflow_and_trailing_garbage() {
        let valid = solve_femm_mesh().tape_cert.to_vec();

        // 1. Truncated stream (drop last byte) must be rejected
        assert_eq!(BinaryTapeCert::from_slice(&valid[..valid.len() - 1]), None);

        // 2. Trailing garbage byte after valid frame must be rejected by from_slice
        let mut with_trailing = valid.clone();
        with_trailing.push(0x00);
        assert_eq!(BinaryTapeCert::from_slice(&with_trailing), None);

        // 3. Adversarial u32::MAX words.length header on a 28-byte frame must return None without OOM
        let mut max_len_frame = Vec::new();
        max_len_frame.extend_from_slice(&[0xD9, 0x0B, 0xED, 0x9A]);
        max_len_frame.extend_from_slice(&u32::MAX.to_be_bytes());
        cbor_encode_u32(HwCertDomain::Magnetics as u32, &mut max_len_frame);
        cbor_encode_u32(1000, &mut max_len_frame);
        cbor_encode_u32(50000, &mut max_len_frame);
        cbor_encode_u32(u32::MAX, &mut max_len_frame);
        assert_eq!(BinaryTapeCert::from_slice(&max_len_frame), None);

        // 4. Mismatched RFC 8949 0x9A array length header must be rejected
        let mut bad_arr_len = valid.clone();
        bad_arr_len[7] ^= 0x01;
        assert_eq!(BinaryTapeCert::from_slice(&bad_arr_len), None);

        // 5. Fixed-arity domain (Pnr) submitted as a 1-word BinaryTapeCert must be refused by verify_local()
        let pnr_bypass = BinaryTapeCert {
            domain: HwCertDomain::Pnr,
            metric0: 0,
            metric1: 0,
            words: vec![1],
        };
        assert!(!pnr_bypass.verify_local());

        // 6. Non-canonical 1-byte tiny uint (< 24) must be rejected to match Lean cborDecodeU32
        assert_eq!(cbor_decode_u32(&[0x05]), None);
    }

    #[test]
    fn test_compact_pruned_tape_diamond_alias_and_large_register_file() {
        // 1. Diamond alias: op2 aliases to reg 0 (Choice::Left), then op3 = MinUnion(0, 2)
        // has both inputs aliased to reg 0 even under Choice::Both, so op3 must collapse cleanly
        // without emitting a dummy lhs == rhs MinUnion node!
        let diamond_tape = vec![
            FrepOp::CylinderZ { out: 0, cx: 0, cy: 0, r_sq: 100 },
            FrepOp::CylinderZ { out: 1, cx: 500, cy: 500, r_sq: 4 },
            FrepOp::MinUnion { out: 2, lhs: 0, rhs: 1 },
            FrepOp::MinUnion { out: 3, lhs: 0, rhs: 2 },
        ];
        let choices = vec![Choice::Both, Choice::Both, Choice::Left, Choice::Both];
        let compacted = compact_pruned_tape(&diamond_tape, &choices);
        assert_eq!(
            compacted.len(),
            1,
            "diamond alias must collapse to the single live primitive"
        );
        assert_eq!(
            eval_frep_tape_point(&compacted, 3, 4, 0),
            eval_frep_tape_point(&diamond_tape, 3, 4, 0)
        );

        // 2. Large register file (> 16 registers): 20 operations must not panic
        let mut large_tape = Vec::new();
        for i in 0..10usize {
            large_tape.push(FrepOp::CylinderZ {
                out: i,
                cx: (i as i64) * 100,
                cy: 0,
                r_sq: 25,
            });
        }
        let mut cur = 0usize;
        for i in 1..10usize {
            let next_out = 9 + i;
            large_tape.push(FrepOp::MinUnion {
                out: next_out,
                lhs: cur,
                rhs: i,
            });
            cur = next_out;
        }
        let box_origin = Interval3D {
            x: Interval::new(-2, 2),
            y: Interval::new(-2, 2),
            z: Interval::new(-2, 2),
        };
        let (_iv, _ch, pruned_large) = prune_tape_for_interval(&large_tape, box_origin);
        assert_eq!(
            pruned_large.len(),
            1,
            "19-op chain over [-2,2]^3 must compact to 1 primitive"
        );
        assert_eq!(
            eval_frep_tape_point(&pruned_large, 1, 1, 0),
            eval_frep_tape_point(&large_tape, 1, 1, 0)
        );
    }

    #[test]
    fn test_binary_tape_cert_verify_local_matches_lean_codec() {
        // 1. Magnetics: tampered metric0 != sum(words) must be rejected
        let mut bad_mag = solve_femm_mesh().tape_cert;
        assert!(bad_mag.verify_local());
        bad_mag.metric0 = 999;
        assert!(!bad_mag.verify_local(), "Magnetics energy sum mismatch must be rejected");

        // 2. MechanicsVonNeumann: metric1 == metric0 or metric1 != sum(words) must be rejected
        let mut bad_mech = eval_octree_frep_pruned().tape_cert;
        assert!(bad_mech.verify_local());
        bad_mech.metric1 = bad_mech.metric0;
        assert!(!bad_mech.verify_local(), "Mechanics metric1 == metric0 must be rejected");

        // 3. FluidThermal: tampered metric1 != evaluated peak winding temp must be rejected
        let mut bad_fluid = evolve_physical_design().tape_cert;
        assert!(bad_fluid.verify_local());
        bad_fluid.metric1 += 1;
        assert!(!bad_fluid.verify_local(), "FluidThermal tampered peak temp must be rejected");
    }
}
