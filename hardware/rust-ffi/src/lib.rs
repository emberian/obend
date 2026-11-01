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

/// Decode RFC 8949 CBOR Major Type 0 unsigned integer (`0x1A` + 4-byte BE, or tiny `< 24`).
pub fn cbor_decode_u32(input: &[u8]) -> Option<(u32, &[u8])> {
    let (&tag, rest) = input.split_first()?;
    if tag == 0x1A {
        if rest.len() < 4 {
            return None;
        }
        let n = u32::from_be_bytes([rest[0], rest[1], rest[2], rest[3]]);
        Some((n, &rest[4..]))
    } else if tag < 24 {
        Some((tag as u32, rest))
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
}
