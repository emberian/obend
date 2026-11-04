//! `obend-node::judge_witness` — Fail-Closed Turn Judge Witness Registry & Verifier.
//!
//! Mirrors Lean's `Obend.Vault.Hyperedge.TurnWitness` / `VaultTurn.witnesses`,
//! `findJudgeFormat`, and `checkBytes` (`Obend.Judge.registry` & `Obend.Logic.Obligation`):
//! - Every `VaultTurn` carries `witnesses: Vec<TurnJudgeWitness>` (`format_tag`, `grade`,
//!   `object_payload`, `cert_payload`).
//! - During BFT proposal, vote, fast-path acknowledgement, and commit, every cited witness
//!   is validated **fail-closed**:
//!   - Refuses malformed or unversioned `format_tag`s,
//!   - Refuses unknown formats not in the registered kernel format table,
//!   - Refuses empty (`""`, `"{}"`, `"[]"`) or malformed JSON payloads,
//!   - Verifies full domain semantics for `"drex-clearing@1"` (and alias `"clearing@1"`),
//!     `"world-carry@1"`, `"interval@1"`, and `"rtl-synth@1"` (and alias `"hw-rtl-synth@1"`).

use crate::{
    cshake256_domain, has_crossing_pair, net_flow, price_in_crossing_interval,
    DrexClearingCertificate, LimitOrder, OrderSide, ResourceTransfer,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// Explicit certificate witness attached to a `VaultTurn`, matching Lean's
/// `Obend.Vault.Hyperedge.TurnWitness` (`formatTag`, `grade`, `objectPayload`, `certPayload`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnJudgeWitness {
    pub format_tag: String,
    pub grade: u32,
    pub object_payload: String,
    pub cert_payload: String,
}

/// Fail-closed witness verification errors returned during BFT proposal, vote, or commit.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
pub enum JudgeWitnessError {
    #[error("invalid witness format_tag '{format_tag}': must be '<domain>@<positive_version>'")]
    InvalidFormatTag { format_tag: String },

    #[error("unknown judge format_tag '{format_tag}' (refused fail-closed by registry)")]
    UnknownFormatTag { format_tag: String },

    #[error("empty or trivial JSON payload in '{format_tag}' ({field})")]
    EmptyOrTrivialPayload {
        format_tag: String,
        field: &'static str,
    },

    #[error("malformed JSON in '{format_tag}' ({field}): {reason}")]
    MalformedJson {
        format_tag: String,
        field: &'static str,
        reason: String,
    },

    #[error("judge '{format_tag}' rejected certificate: {reason}")]
    CertificateRejected { format_tag: String, reason: String },
}

// ============================================================================
// 1. `"drex-clearing@1"` / `"clearing@1"` Primal-Dual LP & Conservation Schema
// ============================================================================

/// Query object payload for `"drex-clearing@1"` / `"clearing@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DrexClearingWitnessObject {
    pub currency: String,
    pub goods: String,
    #[serde(default)]
    pub epsilon: u64,
    pub orders: Vec<LimitOrder>,
}

/// Nested `market` helper supporting Lean's `ClearingQuery` JSON layout (`{"market": {...}, "orders": [...]}`).
#[derive(Debug, Clone, Deserialize)]
struct LeanClearingMarketJson {
    currency: String,
    goods: String,
    #[serde(default)]
    epsilon: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct LeanOrderJson {
    account: String,
    side: String,
    qty: u64,
    total: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct FlexibleClearingObjectJson {
    #[serde(default)]
    currency: Option<String>,
    #[serde(default)]
    goods: Option<String>,
    #[serde(default)]
    epsilon: Option<u64>,
    #[serde(default)]
    market: Option<LeanClearingMarketJson>,
    orders: Vec<LeanOrderJson>,
}

#[derive(Debug, Clone, Deserialize)]
struct FlexibleClearingCertJson {
    #[serde(default)]
    schema: Option<String>,
    #[serde(default)]
    currency: Option<String>,
    #[serde(default)]
    goods: Option<String>,
    #[serde(default)]
    epsilon: Option<u64>,
    price: u64,
    potentials: (i64, i64),
    slacks: Vec<i64>,
    #[serde(default)]
    fills: Option<Vec<u64>>,
    transfers: Vec<ResourceTransfer>,
    #[serde(default)]
    objective_volume: Option<i64>,
    #[serde(default)]
    dual_capacity: Option<i64>,
    #[serde(default)]
    duality_gap: Option<i64>,
    #[serde(default)]
    digest: Option<[u8; 32]>,
}

fn parse_order_side(raw: &str) -> Option<OrderSide> {
    match raw {
        "Bid" | "bid" | "BID" => Some(OrderSide::Bid),
        "Ask" | "ask" | "ASK" => Some(OrderSide::Ask),
        _ => None,
    }
}

fn verify_drex_clearing_witness(
    format_tag: &str,
    _grade: u32,
    object_payload: &str,
    cert_payload: &str,
) -> Result<(), JudgeWitnessError> {
    let raw_obj: FlexibleClearingObjectJson =
        serde_json::from_str(object_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "object_payload",
            reason: e.to_string(),
        })?;

    let (currency, goods, epsilon) = if let Some(m) = raw_obj.market {
        (m.currency, m.goods, m.epsilon)
    } else {
        let c = raw_obj
            .currency
            .ok_or_else(|| JudgeWitnessError::MalformedJson {
                format_tag: format_tag.to_string(),
                field: "object_payload",
                reason: "missing 'currency' or 'market'".to_string(),
            })?;
        let g = raw_obj
            .goods
            .ok_or_else(|| JudgeWitnessError::MalformedJson {
                format_tag: format_tag.to_string(),
                field: "object_payload",
                reason: "missing 'goods' or 'market'".to_string(),
            })?;
        (c, g, raw_obj.epsilon.unwrap_or(0))
    };

    if currency.trim().is_empty() || goods.trim().is_empty() || currency == goods {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "marketMalformed: currency and goods must be non-empty and distinct"
                .to_string(),
        });
    }
    if raw_obj.orders.is_empty() {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "orders list must be non-empty".to_string(),
        });
    }

    let mut orders = Vec::with_capacity(raw_obj.orders.len());
    for o in raw_obj.orders {
        let Some(side) = parse_order_side(&o.side) else {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("invalid order side '{}'", o.side),
            });
        };
        if o.account.trim().is_empty() || o.qty == 0 {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "order must have non-empty account and qty > 0".to_string(),
            });
        }
        orders.push(LimitOrder {
            account: o.account,
            side,
            qty: o.qty,
            total: o.total,
        });
    }

    let cert: FlexibleClearingCertJson =
        serde_json::from_str(cert_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "cert_payload",
            reason: e.to_string(),
        })?;

    if let Some(ref schema) = cert.schema {
        if schema != "drex-clearing@1" && schema != "clearing@1" {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("unexpected cert schema '{schema}'"),
            });
        }
    }
    if let Some(ref c_curr) = cert.currency {
        if c_curr != &currency {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "cert currency does not match object currency".to_string(),
            });
        }
    }
    if let Some(ref c_goods) = cert.goods {
        if c_goods != &goods {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "cert goods does not match object goods".to_string(),
            });
        }
    }
    if let Some(c_eps) = cert.epsilon {
        if c_eps != epsilon {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "cert epsilon does not match object epsilon".to_string(),
            });
        }
    }

    // Check 2: foreignAsset
    if cert
        .transfers
        .iter()
        .any(|t| t.asset != currency && t.asset != goods)
    {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "foreignAsset: transfer references asset outside (currency, goods)".to_string(),
        });
    }

    // Check 3: notAnOrder
    let is_order_account = |acct: &str| orders.iter().any(|o| o.account == acct);
    if cert
        .transfers
        .iter()
        .any(|t| !is_order_account(&t.source) || !is_order_account(&t.destination))
    {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "notAnOrder: transfer endpoint is not an order account".to_string(),
        });
    }

    // Check 4: invalidPrice
    if !price_in_crossing_interval(&orders, cert.price) {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "invalidPrice: clearing price outside crossing interval".to_string(),
        });
    }

    // Check 5: slackCount & fills length
    if cert.slacks.len() != orders.len() {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "slackCount: slacks length does not match orders length".to_string(),
        });
    }
    if let Some(ref fills) = cert.fills {
        if fills.len() != orders.len() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "fills length does not match orders length".to_string(),
            });
        }
    }

    let order_fill = |o: &LimitOrder| -> i64 {
        let nf = net_flow(&cert.transfers, &o.account, &goods);
        match o.side {
            OrderSide::Bid => nf,
            OrderSide::Ask => -nf,
        }
    };
    let order_paid = |o: &LimitOrder| -> i64 {
        let nf = net_flow(&cert.transfers, &o.account, &currency);
        match o.side {
            OrderSide::Bid => -nf,
            OrderSide::Ask => nf,
        }
    };

    // Check 6, 7, 8: uniform price, primal capacity, dual feasibility
    let dual_diff = (cert.potentials.1 as i128) - (cert.potentials.0 as i128);
    let mut obj_vol = 0i128;
    let mut dual_cap = 0i128;
    let mut signed_flow = 0i128;

    for (i, o) in orders.iter().enumerate() {
        let f = order_fill(o) as i128;
        let paid = order_paid(o) as i128;
        if let Some(ref fills) = cert.fills {
            if f != (fills[i] as i128) {
                return Err(JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: format!("order {i} fill mismatch against cert.fills"),
                });
            }
        }
        if paid != (cert.price as i128) * f {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("notUniform: order {i} paid != price * fill"),
            });
        }
        let cap = if o.crosses(cert.price) {
            o.qty as i128
        } else {
            0
        };
        if f < 0 || f > cap {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("capacityExceeded / negativeFill on order {i}"),
            });
        }
        let s = cert.slacks[i] as i128;
        if s < 0 {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("negativeSlack on order {i}"),
            });
        }
        match o.side {
            OrderSide::Bid => {
                if dual_diff + s < 1 {
                    return Err(JudgeWitnessError::CertificateRejected {
                        format_tag: format_tag.to_string(),
                        reason: format!("dualInfeasible on bid order {i}"),
                    });
                }
                signed_flow += f;
            }
            OrderSide::Ask => {
                if -dual_diff + s < 1 {
                    return Err(JudgeWitnessError::CertificateRejected {
                        format_tag: format_tag.to_string(),
                        reason: format!("dualInfeasible on ask order {i}"),
                    });
                }
                signed_flow -= f;
            }
        }
        obj_vol += f;
        dual_cap += cap * s;
    }

    // Check 9: conservation
    if signed_flow != 0 {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "nonConserving: net matched goods flow != 0".to_string(),
        });
    }

    // Check 10: duality gap
    let gap = dual_cap - obj_vol;
    if gap < 0 || gap > (epsilon as i128) {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: format!("uncertified: duality gap {gap} exceeds epsilon {epsilon}"),
        });
    }
    if let Some(expected_obj) = cert.objective_volume {
        if obj_vol != (expected_obj as i128) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "objective_volume mismatch".to_string(),
            });
        }
    }
    if let Some(expected_dual) = cert.dual_capacity {
        if dual_cap != (expected_dual as i128) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "dual_capacity mismatch".to_string(),
            });
        }
    }
    if let Some(expected_gap) = cert.duality_gap {
        if gap != (expected_gap as i128) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "duality_gap mismatch".to_string(),
            });
        }
    }

    // Check 11: unservedCrossing
    if obj_vol == 0 && has_crossing_pair(&orders) {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "unservedCrossing: zero volume despite crossing bid/ask pair".to_string(),
        });
    }

    // Check 12: digest binding if present
    if let Some(digest) = cert.digest {
        let obj_i64 = i64::try_from(obj_vol).map_err(|_| JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "objective_volume overflow".to_string(),
        })?;
        let expected_digest = cshake256_domain(
            b"drex-clearing@1",
            &cert.price.to_be_bytes(),
            &obj_i64.to_be_bytes(),
        );
        if digest != expected_digest {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "clearing certificate cSHAKE256 digest mismatch".to_string(),
            });
        }
    }

    Ok(())
}

// ============================================================================
// 2. `"world-carry@1"` (`K-CARRY` Live Schema/Law Hot-Upgrade Judge)
// ============================================================================

/// Cell entry in a `"world-carry@1"` live world snapshot (`Obend.Vault.Carry.LiveWorld`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldCarryCellSpec {
    pub name: String,
    pub mandate_crown: String,
    pub balance: u64,
    pub schema_ver: u32,
}

/// Zoe seat safety snapshot carried across a `"world-carry@1"` `K-CARRY` transition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldCarrySeatSpec {
    pub seat_id: String,
    pub cbdc_escrow: u64,
    pub bond_escrow: u64,
    pub welfare_crown: u64,
    pub min_cbdc_out: u64,
    pub min_bond_out: u64,
}

/// Object payload for `"world-carry@1"` (`LiveWorld` pre-upgrade state).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldCarryObject {
    pub epoch: u64,
    pub law_pin_digest: u64,
    pub genesis_carry_hash: [u8; 32],
    pub cells: Vec<WorldCarryCellSpec>,
    #[serde(default)]
    pub seats: Vec<WorldCarrySeatSpec>,
    pub total_supply: u64,
}

/// Certificate payload for `"world-carry@1"` (`CarryPlan` migration witness).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorldCarryCert {
    pub from_epoch: u64,
    pub target_epoch: u64,
    pub from_law_pin_digest: u64,
    pub to_law_pin_digest: u64,
    pub genesis_carry_hash: [u8; 32],
    pub kept_cells: Vec<WorldCarryCellSpec>,
    pub named_drops: Vec<String>,
    #[serde(default)]
    pub rehydrated_refs: Vec<String>,
    #[serde(default)]
    pub migrated_seats: Vec<WorldCarrySeatSpec>,
    pub post_total_supply: u64,
}

fn is_forever_crown(cell: &WorldCarryCellSpec) -> bool {
    cell.mandate_crown == "forever"
        || cell.mandate_crown == "forever_welfare_crown"
        || cell.name == "cell.treasury"
}

fn verify_world_carry_witness(
    format_tag: &str,
    _grade: u32,
    object_payload: &str,
    cert_payload: &str,
) -> Result<(), JudgeWitnessError> {
    let obj: WorldCarryObject =
        serde_json::from_str(object_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "object_payload",
            reason: e.to_string(),
        })?;
    let cert: WorldCarryCert =
        serde_json::from_str(cert_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "cert_payload",
            reason: e.to_string(),
        })?;

    if obj.cells.is_empty() {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "pre-upgrade LiveWorld must contain at least one cell".to_string(),
        });
    }
    if cert.from_epoch != obj.epoch || cert.target_epoch <= cert.from_epoch {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: format!(
                "monotone_carry_epoch violated: obj.epoch={}, from_epoch={}, target_epoch={}",
                obj.epoch, cert.from_epoch, cert.target_epoch
            ),
        });
    }
    if obj.law_pin_digest == 0
        || cert.from_law_pin_digest != obj.law_pin_digest
        || cert.to_law_pin_digest == 0
        || cert.to_law_pin_digest == cert.from_law_pin_digest
    {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "invalid K-CARRY law_pin_digest transition".to_string(),
        });
    }
    if cert.genesis_carry_hash != obj.genesis_carry_hash {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "write_once_genesis_carry_hash violated across K-CARRY".to_string(),
        });
    }

    // Index pre-upgrade cells and reject duplicate cell names
    let mut pre_map: BTreeMap<&str, &WorldCarryCellSpec> = BTreeMap::new();
    let mut pre_sum = 0u64;
    for cell in &obj.cells {
        if cell.name.trim().is_empty() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "empty cell name in LiveWorld".to_string(),
            });
        }
        if pre_map.insert(cell.name.as_str(), cell).is_some() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("duplicate pre-upgrade cell '{}'", cell.name),
            });
        }
        pre_sum =
            pre_sum
                .checked_add(cell.balance)
                .ok_or_else(|| JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: "pre-upgrade cell balance overflow".to_string(),
                })?;
    }

    if pre_sum != obj.total_supply {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: format!(
                "pre-upgrade cell sum ({pre_sum}) != obj.total_supply ({})",
                obj.total_supply
            ),
        });
    }

    let mut kept_map: BTreeMap<&str, &WorldCarryCellSpec> = BTreeMap::new();
    let mut post_sum = 0u64;
    for cell in &cert.kept_cells {
        if cell.name.trim().is_empty() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "empty cell name in kept_cells".to_string(),
            });
        }
        if kept_map.insert(cell.name.as_str(), cell).is_some() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("duplicate kept cell '{}'", cell.name),
            });
        }
        post_sum = post_sum.checked_add(cell.balance).ok_or_else(|| {
            JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "post-upgrade cell balance overflow".to_string(),
            }
        })?;
    }

    let mut drop_set: BTreeSet<&str> = BTreeSet::new();
    for dropped in &cert.named_drops {
        if !drop_set.insert(dropped.as_str()) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("duplicate named_drop '{dropped}'"),
            });
        }
        if kept_map.contains_key(dropped.as_str()) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("cell '{dropped}' cannot be both kept and named_dropped"),
            });
        }
        let Some(pre_cell) = pre_map.get(dropped.as_str()) else {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("named_drop '{dropped}' does not exist in pre-upgrade LiveWorld"),
            });
        };
        if is_forever_crown(pre_cell) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("foreverCrown cell '{dropped}' cannot be dropped in K-CARRY"),
            });
        }
        if pre_cell.balance != 0 {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!(
                    "dropped cell '{dropped}' has non-zero balance ({})",
                    pre_cell.balance
                ),
            });
        }
    }

    // Check zero silent cell drops & foreverCrown monotonicity
    for (name, pre_cell) in &pre_map {
        match kept_map.get(name) {
            Some(post_cell) => {
                if is_forever_crown(pre_cell)
                    && (post_cell.mandate_crown != pre_cell.mandate_crown
                        || post_cell.balance < pre_cell.balance)
                {
                    return Err(JudgeWitnessError::CertificateRejected {
                        format_tag: format_tag.to_string(),
                        reason: format!(
                            "foreverCrown cell '{name}' weakened or lost balance during K-CARRY"
                        ),
                    });
                }
                if post_cell.schema_ver < pre_cell.schema_ver {
                    return Err(JudgeWitnessError::CertificateRejected {
                        format_tag: format_tag.to_string(),
                        reason: format!("cell '{name}' schema_ver regressed during K-CARRY"),
                    });
                }
            }
            None => {
                if !drop_set.contains(name) {
                    return Err(JudgeWitnessError::CertificateRejected {
                        format_tag: format_tag.to_string(),
                        reason: format!(
                            "silentCellDrop: cell '{name}' missing from kept_cells and named_drops"
                        ),
                    });
                }
            }
        }
    }

    // Rehydrated references must exist in kept_cells and not in named_drops
    for r in &cert.rehydrated_refs {
        if drop_set.contains(r.as_str()) || !kept_map.contains_key(r.as_str()) {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!(
                    "dangling rehydrated_ref '{r}' (dropped or missing from kept_cells)"
                ),
            });
        }
    }

    // Exact supply conservation
    if post_sum != cert.post_total_supply || cert.post_total_supply != obj.total_supply {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: format!(
                "conserve_total_cbdc_supply violated: pre={}, post_sum={post_sum}, post_total={}",
                obj.total_supply, cert.post_total_supply
            ),
        });
    }

    // Zoe seat offer-safety & aggregate seat conservation if seats are specified
    if !obj.seats.is_empty() || !cert.migrated_seats.is_empty() {
        if obj.seats.len() != cert.migrated_seats.len() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "seat count mismatch across K-CARRY migration".to_string(),
            });
        }
        let mut pre_cbdc = 0u64;
        let mut pre_bond = 0u64;
        let mut pre_welfare = 0u64;
        let mut seat_map: BTreeMap<&str, &WorldCarrySeatSpec> = BTreeMap::new();
        for s in &obj.seats {
            if seat_map.insert(s.seat_id.as_str(), s).is_some() {
                return Err(JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: format!("duplicate seat_id '{}'", s.seat_id),
                });
            }
            pre_cbdc += s.cbdc_escrow;
            pre_bond += s.bond_escrow;
            pre_welfare += s.welfare_crown;
        }

        let mut post_cbdc = 0u64;
        let mut post_bond = 0u64;
        let mut post_welfare = 0u64;
        for ms in &cert.migrated_seats {
            let Some(pre_s) = seat_map.get(ms.seat_id.as_str()) else {
                return Err(JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: format!("unknown migrated seat '{}'", ms.seat_id),
                });
            };
            if ms.welfare_crown < 1000 || ms.welfare_crown < pre_s.welfare_crown {
                return Err(JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: format!("welfare_crown floor violated on seat '{}'", ms.seat_id),
                });
            }
            if ms.cbdc_escrow < ms.min_cbdc_out || ms.bond_escrow < ms.min_bond_out {
                return Err(JudgeWitnessError::CertificateRejected {
                    format_tag: format_tag.to_string(),
                    reason: format!("Zoe offer-safety violated on seat '{}'", ms.seat_id),
                });
            }
            post_cbdc += ms.cbdc_escrow;
            post_bond += ms.bond_escrow;
            post_welfare += ms.welfare_crown;
        }
        if pre_cbdc != post_cbdc || pre_bond != post_bond || pre_welfare != post_welfare {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: "seat CBDC/Bond/Welfare aggregate supply not conserved across K-CARRY"
                    .to_string(),
            });
        }
    }

    Ok(())
}

// ============================================================================
// 3. `"interval@1"` Exact Rational Interval Arithmetic Judge (`Obend.Elab.AutoCert`)
// ============================================================================

/// Exact reduced rational `num / den` (`den > 0`) for `"interval@1"` enclosure proofs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalBound {
    pub num: i128,
    pub den: i128,
}

impl RationalBound {
    pub fn from_int(n: i64) -> Self {
        Self {
            num: n as i128,
            den: 1,
        }
    }

    pub fn new(num: i128, den: i128) -> Option<Self> {
        if den <= 0 {
            return None;
        }
        Some(Self::normalize(num, den))
    }

    fn gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a.max(1)
    }

    fn normalize(num: i128, den: i128) -> Self {
        if num == 0 {
            return Self { num: 0, den: 1 };
        }
        let g = Self::gcd(num.unsigned_abs(), den.unsigned_abs()) as i128;
        Self {
            num: num / g,
            den: den / g,
        }
    }

    fn le(self, rhs: Self) -> bool {
        self.num.saturating_mul(rhs.den) <= rhs.num.saturating_mul(self.den)
    }

    fn min(self, rhs: Self) -> Self {
        if self.le(rhs) {
            self
        } else {
            rhs
        }
    }

    fn max(self, rhs: Self) -> Self {
        if self.le(rhs) {
            rhs
        } else {
            self
        }
    }

    fn add(self, rhs: Self) -> Option<Self> {
        let num = self
            .num
            .checked_mul(rhs.den)?
            .checked_add(rhs.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(rhs.den)?;
        Self::new(num, den)
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        let num = self
            .num
            .checked_mul(rhs.den)?
            .checked_sub(rhs.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(rhs.den)?;
        Self::new(num, den)
    }

    fn mul(self, rhs: Self) -> Option<Self> {
        let num = self.num.checked_mul(rhs.num)?;
        let den = self.den.checked_mul(rhs.den)?;
        Self::new(num, den)
    }

    fn midpoint(self, rhs: Self) -> Option<Self> {
        let sum = self.add(rhs)?;
        Self::new(sum.num, sum.den.checked_mul(2)?)
    }
}

/// Closed rational interval `[lo, hi]` with `lo <= hi`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalInterval {
    pub lo: RationalBound,
    pub hi: RationalBound,
}

impl RationalInterval {
    pub fn from_ints(lo: i64, hi: i64) -> Self {
        Self {
            lo: RationalBound::from_int(lo),
            hi: RationalBound::from_int(hi),
        }
    }

    pub fn is_valid(self) -> bool {
        self.lo.den > 0 && self.hi.den > 0 && self.lo.le(self.hi)
    }

    pub fn subset_of(self, outer: Self) -> bool {
        outer.lo.le(self.lo) && self.hi.le(outer.hi)
    }
}

/// Polynomial/rational expression AST for `"interval@1"` (`Obend.Elab.AutoCert.ArithExpr`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum IntervalExpr {
    Const { val: RationalBound },
    Var { name: String },
    Add { lhs: Box<IntervalExpr>, rhs: Box<IntervalExpr> },
    Sub { lhs: Box<IntervalExpr>, rhs: Box<IntervalExpr> },
    Mul { lhs: Box<IntervalExpr>, rhs: Box<IntervalExpr> },
    Sqr { arg: Box<IntervalExpr> },
}

/// Variable box entry in `"interval@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntervalVarBox {
    pub var: String,
    pub interval: RationalInterval,
}

/// Object payload for `"interval@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntervalWitnessObject {
    pub expr: IntervalExpr,
    pub env: Vec<IntervalVarBox>,
    pub claimed_bound: RationalInterval,
}

/// Certificate tree for `"interval@1"` (`direct` interval evaluation or recursive `bisect`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IntervalWitnessCert {
    Direct,
    Bisect {
        var: String,
        left: Box<IntervalWitnessCert>,
        right: Box<IntervalWitnessCert>,
    },
}

fn eval_interval_expr(
    expr: &IntervalExpr,
    env: &BTreeMap<String, RationalInterval>,
) -> Option<RationalInterval> {
    match expr {
        IntervalExpr::Const { val } => {
            let v = RationalBound::new(val.num, val.den)?;
            Some(RationalInterval { lo: v, hi: v })
        }
        IntervalExpr::Var { name } => env.get(name).copied(),
        IntervalExpr::Add { lhs, rhs } => {
            let a = eval_interval_expr(lhs, env)?;
            let b = eval_interval_expr(rhs, env)?;
            Some(RationalInterval {
                lo: a.lo.add(b.lo)?,
                hi: a.hi.add(b.hi)?,
            })
        }
        IntervalExpr::Sub { lhs, rhs } => {
            let a = eval_interval_expr(lhs, env)?;
            let b = eval_interval_expr(rhs, env)?;
            Some(RationalInterval {
                lo: a.lo.sub(b.hi)?,
                hi: a.hi.sub(b.lo)?,
            })
        }
        IntervalExpr::Mul { lhs, rhs } => {
            let a = eval_interval_expr(lhs, env)?;
            let b = eval_interval_expr(rhs, env)?;
            let p1 = a.lo.mul(b.lo)?;
            let p2 = a.lo.mul(b.hi)?;
            let p3 = a.hi.mul(b.lo)?;
            let p4 = a.hi.mul(b.hi)?;
            let lo = p1.min(p2).min(p3).min(p4);
            let hi = p1.max(p2).max(p3).max(p4);
            Some(RationalInterval { lo, hi })
        }
        IntervalExpr::Sqr { arg } => {
            let a = eval_interval_expr(arg, env)?;
            let lo_sq = a.lo.mul(a.lo)?;
            let hi_sq = a.hi.mul(a.hi)?;
            let hi = lo_sq.max(hi_sq);
            let zero = RationalBound::from_int(0);
            let lo = if a.lo.le(zero) && zero.le(a.hi) {
                zero
            } else {
                lo_sq.min(hi_sq)
            };
            Some(RationalInterval { lo, hi })
        }
    }
}

fn check_interval_cert(
    expr: &IntervalExpr,
    env: &BTreeMap<String, RationalInterval>,
    claimed: RationalInterval,
    cert: &IntervalWitnessCert,
    remaining_depth: u32,
) -> Result<(), String> {
    match cert {
        IntervalWitnessCert::Direct => {
            let evaluated = eval_interval_expr(expr, env)
                .ok_or_else(|| "unbound variable or rational overflow in interval expr".to_string())?;
            if evaluated.subset_of(claimed) {
                Ok(())
            } else {
                Err(format!(
                    "interval enclosure failed: [{}/{}, {}/{}] not subset of [{}/{}, {}/{}]",
                    evaluated.lo.num,
                    evaluated.lo.den,
                    evaluated.hi.num,
                    evaluated.hi.den,
                    claimed.lo.num,
                    claimed.lo.den,
                    claimed.hi.num,
                    claimed.hi.den
                ))
            }
        }
        IntervalWitnessCert::Bisect { var, left, right } => {
            if remaining_depth == 0 {
                return Err("interval bisection exceeded witness grade depth".to_string());
            }
            let cur = env
                .get(var)
                .copied()
                .ok_or_else(|| format!("bisect variable '{var}' missing from env"))?;
            let mid = cur
                .lo
                .midpoint(cur.hi)
                .ok_or_else(|| "midpoint overflow".to_string())?;
            let mut left_env = env.clone();
            left_env.insert(var.clone(), RationalInterval { lo: cur.lo, hi: mid });
            let mut right_env = env.clone();
            right_env.insert(var.clone(), RationalInterval { lo: mid, hi: cur.hi });
            check_interval_cert(expr, &left_env, claimed, left, remaining_depth - 1)?;
            check_interval_cert(expr, &right_env, claimed, right, remaining_depth - 1)
        }
    }
}

fn verify_interval_witness(
    format_tag: &str,
    grade: u32,
    object_payload: &str,
    cert_payload: &str,
) -> Result<(), JudgeWitnessError> {
    let obj: IntervalWitnessObject =
        serde_json::from_str(object_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "object_payload",
            reason: e.to_string(),
        })?;
    let cert: IntervalWitnessCert =
        serde_json::from_str(cert_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "cert_payload",
            reason: e.to_string(),
        })?;

    if !obj.claimed_bound.is_valid() {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "claimed_bound interval is invalid (lo > hi or den <= 0)".to_string(),
        });
    }

    let mut env = BTreeMap::new();
    for entry in &obj.env {
        if entry.var.trim().is_empty() || !entry.interval.is_valid() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("invalid box for variable '{}'", entry.var),
            });
        }
        if env.insert(entry.var.clone(), entry.interval).is_some() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("duplicate variable '{}' in interval env", entry.var),
            });
        }
    }

    let max_depth = grade.max(1).min(16);
    check_interval_cert(&obj.expr, &env, obj.claimed_bound, &cert, max_depth).map_err(|reason| {
        JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason,
        }
    })
}

// ============================================================================
// 4. `"rtl-synth@1"` / `"hw-rtl-synth@1"` DAG Acyclicity & CDC Judge
// ============================================================================

/// Combinational signal source in `"rtl-synth@1"` (`Obend.Hardware.Judge.RtlExpr`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RtlSignalRef {
    Const { val: u64 },
    InPort { idx: usize },
    WireRef { idx: usize },
    RegRef { idx: usize },
    Add { a: Box<RtlSignalRef>, b: Box<RtlSignalRef> },
    Mul { a: Box<RtlSignalRef>, b: Box<RtlSignalRef> },
    Xor { a: Box<RtlSignalRef>, b: Box<RtlSignalRef> },
}

/// Combinational wire assignment in `"rtl-synth@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RtlWireDecl {
    pub name: String,
    pub clock_domain: String,
    pub expr: RtlSignalRef,
}

/// Synchronous register declaration in `"rtl-synth@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RtlRegDecl {
    pub name: String,
    pub clock_domain: String,
    pub reset_val: u64,
    #[serde(default)]
    pub synchronizer_stages: u8,
    pub next: RtlSignalRef,
}

/// Output port declaration in `"rtl-synth@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RtlOutputDecl {
    pub name: String,
    pub clock_domain: String,
    pub source: RtlSignalRef,
}

/// Object payload for `"rtl-synth@1"` / `"hw-rtl-synth@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RtlSynthWitnessObject {
    pub module: String,
    pub primary_clock_domain: String,
    pub expected_input_count: usize,
    pub expected_output_count: usize,
}

/// Certificate payload for `"rtl-synth@1"` / `"hw-rtl-synth@1"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RtlSynthWitnessCert {
    pub module: String,
    pub clock_domain: String,
    pub inputs: Vec<String>,
    pub wires: Vec<RtlWireDecl>,
    #[serde(default)]
    pub regs: Vec<RtlRegDecl>,
    pub outputs: Vec<RtlOutputDecl>,
}

fn check_rtl_signal_dag_and_cdc(
    sig: &RtlSignalRef,
    max_wire_exclusive: usize,
    inputs_len: usize,
    wires: &[RtlWireDecl],
    regs: &[RtlRegDecl],
    consumer_domain: &str,
    allow_cdc_sync: bool,
) -> Result<(), String> {
    match sig {
        RtlSignalRef::Const { .. } => Ok(()),
        RtlSignalRef::InPort { idx } => {
            if *idx >= inputs_len {
                Err(format!(
                    "InPort index {idx} out of bounds (inputs_len = {inputs_len})"
                ))
            } else {
                Ok(())
            }
        }
        RtlSignalRef::WireRef { idx } => {
            if *idx >= max_wire_exclusive || *idx >= wires.len() {
                return Err(format!(
                    "combinational cycle or forward WireRef {idx} (allowed < {max_wire_exclusive})"
                ));
            }
            let src_domain = &wires[*idx].clock_domain;
            if src_domain != consumer_domain && !allow_cdc_sync {
                return Err(format!(
                    "unsynchronized CDC crossing from wire '{}' ({src_domain}) into {consumer_domain}",
                    wires[*idx].name
                ));
            }
            Ok(())
        }
        RtlSignalRef::RegRef { idx } => {
            let Some(reg) = regs.get(*idx) else {
                return Err(format!(
                    "RegRef index {idx} out of bounds (regs_len = {})",
                    regs.len()
                ));
            };
            if reg.clock_domain != consumer_domain && !allow_cdc_sync {
                return Err(format!(
                    "unsynchronized CDC crossing from reg '{}' ({}) into {consumer_domain}",
                    reg.name, reg.clock_domain
                ));
            }
            Ok(())
        }
        RtlSignalRef::Add { a, b } | RtlSignalRef::Mul { a, b } | RtlSignalRef::Xor { a, b } => {
            check_rtl_signal_dag_and_cdc(
                a,
                max_wire_exclusive,
                inputs_len,
                wires,
                regs,
                consumer_domain,
                allow_cdc_sync,
            )?;
            check_rtl_signal_dag_and_cdc(
                b,
                max_wire_exclusive,
                inputs_len,
                wires,
                regs,
                consumer_domain,
                allow_cdc_sync,
            )
        }
    }
}

fn verify_rtl_synth_witness(
    format_tag: &str,
    _grade: u32,
    object_payload: &str,
    cert_payload: &str,
) -> Result<(), JudgeWitnessError> {
    let obj: RtlSynthWitnessObject =
        serde_json::from_str(object_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "object_payload",
            reason: e.to_string(),
        })?;
    let cert: RtlSynthWitnessCert =
        serde_json::from_str(cert_payload).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field: "cert_payload",
            reason: e.to_string(),
        })?;

    if obj.module.trim().is_empty() || cert.module != obj.module {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: format!(
                "RTL module mismatch: expected '{}', got '{}'",
                obj.module, cert.module
            ),
        });
    }
    if cert.clock_domain.trim().is_empty() || cert.clock_domain != obj.primary_clock_domain {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "RTL primary clock_domain mismatch".to_string(),
        });
    }
    if cert.inputs.is_empty()
        || cert.outputs.is_empty()
        || cert.inputs.len() != obj.expected_input_count
        || cert.outputs.len() != obj.expected_output_count
    {
        return Err(JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason: "RTL input/output port count mismatch or empty port list".to_string(),
        });
    }

    for (wire_idx, wire) in cert.wires.iter().enumerate() {
        if wire.name.trim().is_empty() || wire.clock_domain.trim().is_empty() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("wire {wire_idx} has empty name or clock_domain"),
            });
        }
        check_rtl_signal_dag_and_cdc(
            &wire.expr,
            wire_idx,
            cert.inputs.len(),
            &cert.wires,
            &cert.regs,
            &wire.clock_domain,
            false,
        )
        .map_err(|reason| JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason,
        })?;
    }

    for (reg_idx, reg) in cert.regs.iter().enumerate() {
        if reg.name.trim().is_empty() || reg.clock_domain.trim().is_empty() {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("reg {reg_idx} has empty name or clock_domain"),
            });
        }
        let allow_cdc = reg.synchronizer_stages >= 2;
        check_rtl_signal_dag_and_cdc(
            &reg.next,
            cert.wires.len(),
            cert.inputs.len(),
            &cert.wires,
            &cert.regs,
            &reg.clock_domain,
            allow_cdc,
        )
        .map_err(|reason| JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason,
        })?;
    }

    for (out_idx, out) in cert.outputs.iter().enumerate() {
        if out.name.trim().is_empty() || out.clock_domain != cert.clock_domain {
            return Err(JudgeWitnessError::CertificateRejected {
                format_tag: format_tag.to_string(),
                reason: format!("output {out_idx} invalid name or clock_domain"),
            });
        }
        check_rtl_signal_dag_and_cdc(
            &out.source,
            cert.wires.len(),
            cert.inputs.len(),
            &cert.wires,
            &cert.regs,
            &out.clock_domain,
            false,
        )
        .map_err(|reason| JudgeWitnessError::CertificateRejected {
            format_tag: format_tag.to_string(),
            reason,
        })?;
    }

    Ok(())
}

// ============================================================================
// 5. Top-Level `findJudgeFormat` & Fail-Closed Dispatch
// ============================================================================

fn validate_format_tag_syntax(tag: &str) -> Result<(), JudgeWitnessError> {
    let Some((domain, ver_str)) = tag.split_once('@') else {
        return Err(JudgeWitnessError::InvalidFormatTag {
            format_tag: tag.to_string(),
        });
    };
    if domain.trim().is_empty()
        || ver_str.contains('@')
        || ver_str.parse::<u32>().ok().filter(|&v| v >= 1).is_none()
    {
        return Err(JudgeWitnessError::InvalidFormatTag {
            format_tag: tag.to_string(),
        });
    }
    Ok(())
}

fn ensure_non_trivial_json(
    format_tag: &str,
    field: &'static str,
    payload: &str,
) -> Result<(), JudgeWitnessError> {
    let trimmed = payload.trim();
    if trimmed.is_empty() || trimmed == "{}" || trimmed == "[]" || trimmed == "null" {
        return Err(JudgeWitnessError::EmptyOrTrivialPayload {
            format_tag: format_tag.to_string(),
            field,
        });
    }
    let val: serde_json::Value =
        serde_json::from_str(trimmed).map_err(|e| JudgeWitnessError::MalformedJson {
            format_tag: format_tag.to_string(),
            field,
            reason: e.to_string(),
        })?;
    match val {
        serde_json::Value::Object(map) if map.is_empty() => {
            Err(JudgeWitnessError::EmptyOrTrivialPayload {
                format_tag: format_tag.to_string(),
                field,
            })
        }
        serde_json::Value::Array(arr) if arr.is_empty() => {
            Err(JudgeWitnessError::EmptyOrTrivialPayload {
                format_tag: format_tag.to_string(),
                field,
            })
        }
        serde_json::Value::Null => Err(JudgeWitnessError::EmptyOrTrivialPayload {
            format_tag: format_tag.to_string(),
            field,
        }),
        _ => Ok(()),
    }
}

/// Validate a single `TurnJudgeWitness` fail-closed against the kernel judge registry
/// (`"drex-clearing@1"` / `"clearing@1"`, `"world-carry@1"`, `"interval@1"`,
/// `"rtl-synth@1"` / `"hw-rtl-synth@1"`).
pub fn verify_turn_witness(witness: &TurnJudgeWitness) -> Result<(), JudgeWitnessError> {
    validate_format_tag_syntax(&witness.format_tag)?;
    ensure_non_trivial_json(&witness.format_tag, "object_payload", &witness.object_payload)?;
    ensure_non_trivial_json(&witness.format_tag, "cert_payload", &witness.cert_payload)?;

    match witness.format_tag.as_str() {
        "drex-clearing@1" | "clearing@1" => verify_drex_clearing_witness(
            &witness.format_tag,
            witness.grade,
            &witness.object_payload,
            &witness.cert_payload,
        ),
        "world-carry@1" => verify_world_carry_witness(
            &witness.format_tag,
            witness.grade,
            &witness.object_payload,
            &witness.cert_payload,
        ),
        "interval@1" => verify_interval_witness(
            &witness.format_tag,
            witness.grade,
            &witness.object_payload,
            &witness.cert_payload,
        ),
        "rtl-synth@1" | "hw-rtl-synth@1" => verify_rtl_synth_witness(
            &witness.format_tag,
            witness.grade,
            &witness.object_payload,
            &witness.cert_payload,
        ),
        _ => Err(JudgeWitnessError::UnknownFormatTag {
            format_tag: witness.format_tag.clone(),
        }),
    }
}

/// Validate every cited `TurnJudgeWitness` in a slice fail-closed (`VaultTurn.ValidAt`).
pub fn verify_all_turn_witnesses(witnesses: &[TurnJudgeWitness]) -> Result<(), JudgeWitnessError> {
    for w in witnesses {
        verify_turn_witness(w)?;
    }
    Ok(())
}

impl TurnJudgeWitness {
    /// Construct a `"drex-clearing@1"` `TurnJudgeWitness` from a batch's `LimitOrder`s and `DrexClearingCertificate`.
    pub fn drex_clearing(
        grade: u32,
        currency: &str,
        goods: &str,
        epsilon: u64,
        orders: &[LimitOrder],
        cert: &DrexClearingCertificate,
    ) -> Self {
        let obj = DrexClearingWitnessObject {
            currency: currency.to_string(),
            goods: goods.to_string(),
            epsilon,
            orders: orders.to_vec(),
        };
        Self {
            format_tag: "drex-clearing@1".to_string(),
            grade,
            object_payload: serde_json::to_string(&obj).expect("DrexClearingWitnessObject JSON"),
            cert_payload: serde_json::to_string(cert).expect("DrexClearingCertificate JSON"),
        }
    }

    /// Construct a `"world-carry@1"` `TurnJudgeWitness` from a pre-upgrade `WorldCarryObject` and `WorldCarryCert`.
    pub fn world_carry(grade: u32, obj: &WorldCarryObject, cert: &WorldCarryCert) -> Self {
        Self {
            format_tag: "world-carry@1".to_string(),
            grade,
            object_payload: serde_json::to_string(obj).expect("WorldCarryObject JSON"),
            cert_payload: serde_json::to_string(cert).expect("WorldCarryCert JSON"),
        }
    }

    /// Construct an `"interval@1"` `TurnJudgeWitness` from an `IntervalWitnessObject` and `IntervalWitnessCert`.
    pub fn interval(grade: u32, obj: &IntervalWitnessObject, cert: &IntervalWitnessCert) -> Self {
        Self {
            format_tag: "interval@1".to_string(),
            grade,
            object_payload: serde_json::to_string(obj).expect("IntervalWitnessObject JSON"),
            cert_payload: serde_json::to_string(cert).expect("IntervalWitnessCert JSON"),
        }
    }

    /// Construct an `"rtl-synth@1"` `TurnJudgeWitness` from an `RtlSynthWitnessObject` and `RtlSynthWitnessCert`.
    pub fn rtl_synth(grade: u32, obj: &RtlSynthWitnessObject, cert: &RtlSynthWitnessCert) -> Self {
        Self {
            format_tag: "rtl-synth@1".to_string(),
            grade,
            object_payload: serde_json::to_string(obj).expect("RtlSynthWitnessObject JSON"),
            cert_payload: serde_json::to_string(cert).expect("RtlSynthWitnessCert JSON"),
        }
    }

    /// Domain-separated 32-byte digest of this witness for `VaultTurn::digest()` and `OBCAMv1` binding.
    pub fn digest(&self) -> [u8; 32] {
        let mut head = Vec::with_capacity(self.format_tag.len() + 12);
        head.extend_from_slice(&(self.format_tag.len() as u64).to_be_bytes());
        head.extend_from_slice(self.format_tag.as_bytes());
        head.extend_from_slice(&self.grade.to_be_bytes());

        let mut body =
            Vec::with_capacity(16 + self.object_payload.len() + self.cert_payload.len());
        body.extend_from_slice(&(self.object_payload.len() as u64).to_be_bytes());
        body.extend_from_slice(self.object_payload.as_bytes());
        body.extend_from_slice(&(self.cert_payload.len() as u64).to_be_bytes());
        body.extend_from_slice(self.cert_payload.as_bytes());

        cshake256_domain(b"obend.turn.judge_witness", &head, &body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solve_primal_dual_clearing;

    #[test]
    fn test_judge_witness_registry_accepts_valid_and_rejects_forged_fail_closed() {
        // 1. Valid drex-clearing@1 witness
        let orders = vec![
            LimitOrder {
                account: "seat_alpha".to_string(),
                side: OrderSide::Bid,
                qty: 20,
                total: 2000,
            },
            LimitOrder {
                account: "seat_beta".to_string(),
                side: OrderSide::Ask,
                qty: 20,
                total: 1960,
            },
        ];
        let cert = solve_primal_dual_clearing("CBDC", "BOND", 0, &orders).unwrap();
        let w_drex = TurnJudgeWitness::drex_clearing(1, "CBDC", "BOND", 0, &orders, &cert);
        assert!(verify_turn_witness(&w_drex).is_ok());

        // Forged drex-clearing@1 witness (corrupted slack -> dual infeasible)
        let mut bad_cert = cert.clone();
        bad_cert.slacks[0] = -1;
        let w_bad_drex =
            TurnJudgeWitness::drex_clearing(1, "CBDC", "BOND", 0, &orders, &bad_cert);
        assert!(matches!(
            verify_turn_witness(&w_bad_drex),
            Err(JudgeWitnessError::CertificateRejected { .. })
        ));

        // 2. Unknown format tag & empty JSON refused fail-closed
        let w_unknown = TurnJudgeWitness {
            format_tag: "magic-oracle@1".to_string(),
            grade: 1,
            object_payload: r#"{"x":1}"#.to_string(),
            cert_payload: r#"{"ok":true}"#.to_string(),
        };
        assert!(matches!(
            verify_turn_witness(&w_unknown),
            Err(JudgeWitnessError::UnknownFormatTag { .. })
        ));

        let w_empty = TurnJudgeWitness {
            format_tag: "world-carry@1".to_string(),
            grade: 1,
            object_payload: "{}".to_string(),
            cert_payload: "{}".to_string(),
        };
        assert!(matches!(
            verify_turn_witness(&w_empty),
            Err(JudgeWitnessError::EmptyOrTrivialPayload { .. })
        ));

        // 3. Valid world-carry@1 vs silent drop & foreverCrown drop
        let pre = WorldCarryObject {
            epoch: 1,
            law_pin_digest: 0x1111,
            genesis_carry_hash: [0xAB; 32],
            cells: vec![
                WorldCarryCellSpec {
                    name: "cell.treasury".to_string(),
                    mandate_crown: "forever".to_string(),
                    balance: 1000,
                    schema_ver: 1,
                },
                WorldCarryCellSpec {
                    name: "cell.scratch".to_string(),
                    mandate_crown: "ephemeral".to_string(),
                    balance: 0,
                    schema_ver: 1,
                },
            ],
            seats: vec![],
            total_supply: 1000,
        };
        let plan_ok = WorldCarryCert {
            from_epoch: 1,
            target_epoch: 2,
            from_law_pin_digest: 0x1111,
            to_law_pin_digest: 0x2222,
            genesis_carry_hash: [0xAB; 32],
            kept_cells: vec![WorldCarryCellSpec {
                name: "cell.treasury".to_string(),
                mandate_crown: "forever".to_string(),
                balance: 1000,
                schema_ver: 2,
            }],
            named_drops: vec!["cell.scratch".to_string()],
            rehydrated_refs: vec!["cell.treasury".to_string()],
            migrated_seats: vec![],
            post_total_supply: 1000,
        };
        let w_carry = TurnJudgeWitness::world_carry(1, &pre, &plan_ok);
        assert!(verify_turn_witness(&w_carry).is_ok());

        // Silent drop (cell.scratch omitted from both kept_cells and named_drops)
        let mut plan_silent_drop = plan_ok.clone();
        plan_silent_drop.named_drops.clear();
        assert!(matches!(
            verify_turn_witness(&TurnJudgeWitness::world_carry(1, &pre, &plan_silent_drop)),
            Err(JudgeWitnessError::CertificateRejected { .. })
        ));

        // 4. Valid interval@1 (x^2 in [0, 2500] for x in [-10, 50]) vs violated bound
        let iv_obj = IntervalWitnessObject {
            expr: IntervalExpr::Sqr {
                arg: Box::new(IntervalExpr::Var {
                    name: "slippage_bps".to_string(),
                }),
            },
            env: vec![IntervalVarBox {
                var: "slippage_bps".to_string(),
                interval: RationalInterval::from_ints(-10, 50),
            }],
            claimed_bound: RationalInterval::from_ints(0, 2500),
        };
        let w_iv = TurnJudgeWitness::interval(2, &iv_obj, &IntervalWitnessCert::Direct);
        assert!(verify_turn_witness(&w_iv).is_ok());

        let mut iv_bad = iv_obj.clone();
        iv_bad.claimed_bound = RationalInterval::from_ints(0, 1000);
        assert!(matches!(
            verify_turn_witness(&TurnJudgeWitness::interval(
                2,
                &iv_bad,
                &IntervalWitnessCert::Direct
            )),
            Err(JudgeWitnessError::CertificateRejected { .. })
        ));

        // 5. Valid rtl-synth@1 vs combinational wire self-loop
        let rtl_obj = RtlSynthWitnessObject {
            module: "sovereign_drex_batch_top".to_string(),
            primary_clock_domain: "clk_250mhz".to_string(),
            expected_input_count: 2,
            expected_output_count: 1,
        };
        let rtl_cert = RtlSynthWitnessCert {
            module: "sovereign_drex_batch_top".to_string(),
            clock_domain: "clk_250mhz".to_string(),
            inputs: vec!["cbdc_in".to_string(), "welfare_floor".to_string()],
            wires: vec![RtlWireDecl {
                name: "sum_w0".to_string(),
                clock_domain: "clk_250mhz".to_string(),
                expr: RtlSignalRef::Add {
                    a: Box::new(RtlSignalRef::InPort { idx: 0 }),
                    b: Box::new(RtlSignalRef::InPort { idx: 1 }),
                },
            }],
            regs: vec![],
            outputs: vec![RtlOutputDecl {
                name: "settled_out".to_string(),
                clock_domain: "clk_250mhz".to_string(),
                source: RtlSignalRef::WireRef { idx: 0 },
            }],
        };
        assert!(verify_turn_witness(&TurnJudgeWitness::rtl_synth(1, &rtl_obj, &rtl_cert)).is_ok());

        let mut rtl_cycle = rtl_cert.clone();
        rtl_cycle.wires[0].expr = RtlSignalRef::WireRef { idx: 0 };
        assert!(matches!(
            verify_turn_witness(&TurnJudgeWitness::rtl_synth(1, &rtl_obj, &rtl_cycle)),
            Err(JudgeWitnessError::CertificateRejected { .. })
        ));
    }
}
