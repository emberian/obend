//! Integration & Qualification Suite for `WS-4C-1`:
//! `crates/obend-node` + `obend-fpga-hal` + 4-Validator `apps/sovereign-drex/` Live Cluster
//! (`QUALIFICATION-AND-SILICON-LEAN.md` Mandate #6, §3.1, §4 Flagship App #7, and Critical Addendum).

use obend_node::{
    cshake256_domain, solve_primal_dual_clearing, verify_turn_witness, ConsensusNetMessage,
    IntervalExpr, IntervalVarBox, IntervalWitnessCert, IntervalWitnessObject, JudgeWitnessError,
    LimitOrder, NodeError, OrderSide, PropCert, RationalInterval, RtlOutputDecl, RtlRegDecl,
    RtlSignalRef, RtlSynthWitnessCert, RtlSynthWitnessObject, RtlWireDecl, SovereignDrexCluster,
    TurnJudgeWitness, VaultTurn, WorldCarryCellSpec, WorldCarryCert, WorldCarryObject,
};
use std::thread;
use std::time::Duration;

#[test]
fn test_sovereign_drex_4_validator_live_cluster_end_to_end_qualification() {
    // =========================================================================
    // 1. Load & Content-Address the 4 Real `.obend` Modules in `apps/sovereign-drex/`
    // =========================================================================
    let mut drex = SovereignDrexCluster::spawn_default()
        .expect("SovereignDrexCluster::spawn_default should load apps/sovereign-drex/ and boot 4 validators");

    assert_eq!(drex.package.package_name, "sovereign-drex");
    assert_eq!(drex.package.entry_module, "SovereignDrexTop.obend");
    assert_eq!(drex.package.modules.len(), 4);

    let file_names: Vec<&str> = drex
        .package
        .modules
        .iter()
        .map(|m| m.file_name.as_str())
        .collect();
    assert_eq!(
        file_names,
        vec![
            "Seat.obend",
            "OrderBook.obend",
            "BatchClearing.obend",
            "SovereignDrexTop.obend"
        ]
    );
    for m in &drex.package.modules {
        assert!(m.byte_len > 100, "{} should not be empty", m.file_name);
        assert_ne!(
            m.sha256_digest, [0u8; 32],
            "{} SHA-256 digest must be non-zero",
            m.file_name
        );
    }
    assert_ne!(drex.package.manifest_root, [0u8; 32]);
    assert_ne!(drex.package.genesis_carry_hash, [0u8; 32]);
    assert_ne!(drex.package.epoch1_law_pin_digest, 0);
    assert_ne!(drex.package.epoch2_law_pin_digest, 0);
    assert_ne!(
        drex.package.epoch1_law_pin_digest,
        drex.package.epoch2_law_pin_digest
    );

    // Verify open-recursion `.obend` specification outputs
    assert_eq!(drex.package.spec_eval.institutional_safety_at_80, 95_000);
    assert_eq!(drex.package.spec_eval.institutional_mandate_at_15, 1_650);
    assert_eq!(drex.package.spec_eval.wholesale_volume_at_20, 127_000);
    assert_eq!(drex.package.spec_eval.wholesale_slack_at_10, 10_040);
    assert_eq!(drex.package.spec_eval.sovereign_cleared_at_12, 7_000);
    assert_eq!(drex.package.spec_eval.sovereign_digest_at_5, 182);
    assert_eq!(drex.package.spec_eval.drex_settlement_at_8, 5_000);
    assert_eq!(drex.package.spec_eval.drex_finality_tag_at_3, 227);
    assert_eq!(drex.package.spec_eval.cross_module_drex_summary, 110_222);

    // Verify all 4 validators' `DurableSimplexHost` + `ObendFpgaHal` boot telemetry
    assert_eq!(drex.boot_obcam_telemetry.len(), 4);
    for (vid, telem) in drex.boot_obcam_telemetry.iter().enumerate() {
        assert!(
            telem.kernel_accepted,
            "validator {vid} ObendFpgaHal must accept boot OBCAMv1 LEB128 wire frame"
        );
        assert!(telem.total_cycles > 0);
        assert!(telem.cam_hits > 0);
        let host_snap = drex.host(vid).unwrap().snapshot().unwrap();
        assert!(host_snap.memory_up);
        assert_eq!(host_snap.active_dpr_epoch_id, 1);
        assert_eq!(
            host_snap.active_law_pin_digest,
            drex.package.epoch1_law_pin_digest
        );
    }

    assert_eq!(drex.initial_total_cbdc_supply, 301_000);
    assert_eq!(drex.initial_total_bond_supply, 125_000);
    assert_eq!(drex.initial_total_welfare_crown, 4_000);

    // =========================================================================
    // 2. Epoch 1 Multi-Seat Order Batches + `"drex-clearing@1"` Witness + Half-Edge Conservation
    // =========================================================================
    // Negative law check: `bounded_seat_slippage: new.slippageBps <= 50`
    let bad_slippage_orders = vec![
        LimitOrder {
            account: "seat_alpha".to_string(),
            side: OrderSide::Bid,
            qty: 10,
            total: 1_000,
        },
        LimitOrder {
            account: "seat_beta".to_string(),
            side: OrderSide::Ask,
            qty: 10,
            total: 980,
        },
    ];
    assert!(
        drex.submit_and_finalize_batch(bad_slippage_orders, 55)
            .is_err(),
        "slippage_bps = 55 > 50 must be rejected fail-closed by bounded_seat_slippage law"
    );

    // Negative collateral check: order exceeding `seat_gamma` CBDC escrow (50,000)
    let excessive_escrow_orders = vec![
        LimitOrder {
            account: "seat_gamma".to_string(),
            side: OrderSide::Bid,
            qty: 100,
            total: 60_000,
        },
        LimitOrder {
            account: "seat_treasury".to_string(),
            side: OrderSide::Ask,
            qty: 100,
            total: 50_000,
        },
    ];
    assert!(
        drex.submit_and_finalize_batch(excessive_escrow_orders, 20)
            .is_err(),
        "order exceeding Zoe seat CBDC escrow must be rejected fail-closed"
    );

    // Epoch 1 Batch #1: multi-seat crossing batch across `seat_alpha`, `seat_beta`, `seat_gamma`, `seat_treasury`
    let epoch1_batch1 = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_alpha".to_string(),
                    side: OrderSide::Bid,
                    qty: 25,
                    total: 2_500, // bid limit 100
                },
                LimitOrder {
                    account: "seat_gamma".to_string(),
                    side: OrderSide::Bid,
                    qty: 15,
                    total: 1_500, // bid limit 100
                },
                LimitOrder {
                    account: "seat_beta".to_string(),
                    side: OrderSide::Ask,
                    qty: 20,
                    total: 1_960, // ask limit 98
                },
                LimitOrder {
                    account: "seat_treasury".to_string(),
                    side: OrderSide::Ask,
                    qty: 20,
                    total: 1_960, // ask limit 98
                },
            ],
            25,
        )
        .expect("Epoch 1 Batch #1 should finalize across 4-validator Simplex quorum");

    assert_eq!(epoch1_batch1.carry_epoch, 1);
    assert_eq!(epoch1_batch1.batch_seq, 1);
    assert_eq!(epoch1_batch1.block_height, 1);
    assert!(epoch1_batch1.quorum_votes >= 3);
    assert_eq!(
        epoch1_batch1.active_law_pin_digest,
        drex.package.epoch1_law_pin_digest
    );
    assert!(
        epoch1_batch1
            .witness_formats
            .contains(&"drex-clearing@1".to_string()),
        "Epoch 1 turn must carry 'drex-clearing@1' TurnJudgeWitness"
    );
    assert!(
        epoch1_batch1
            .witness_formats
            .contains(&"interval@1".to_string())
    );
    assert!(
        epoch1_batch1
            .witness_formats
            .contains(&"rtl-synth@1".to_string())
    );
    assert_eq!(epoch1_batch1.pre_total_cbdc_supply, 301_000);
    assert_eq!(epoch1_batch1.post_total_cbdc_supply, 301_000);
    assert_eq!(epoch1_batch1.pre_total_bond_supply, 125_000);
    assert_eq!(epoch1_batch1.post_total_bond_supply, 125_000);
    assert!(!epoch1_batch1.half_edge_postings.is_empty());
    assert_eq!(
        epoch1_batch1
            .half_edge_postings
            .iter()
            .filter(|p| p.asset == "CBDC")
            .map(|p| p.delta)
            .sum::<i64>(),
        0
    );
    assert_eq!(
        epoch1_batch1
            .half_edge_postings
            .iter()
            .filter(|p| p.asset == "BOND")
            .map(|p| p.delta)
            .sum::<i64>(),
        0
    );
    assert_eq!(epoch1_batch1.validator_telemetry.len(), 4);
    for (&vid, telem) in &epoch1_batch1.validator_telemetry {
        assert!(
            telem.kernel_accepted,
            "validator {vid} hardware kernel_accepted must be true"
        );
        assert!(telem.total_cycles > 0);
        assert!(telem.cam_hits > 0);
        assert!(telem.uram_bypass_hits > 0);
        assert!(telem.noc_flits > 0);
        assert!(telem.discr_lut_hits > 0);
    }
    assert!(
        epoch1_batch1
            .finalized_block
            .silicon_recorded_at_unix_ms
            > 0
    );

    // Epoch 1 Batch #2: second multi-seat order batch in Epoch 1
    let epoch1_batch2 = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_beta".to_string(),
                    side: OrderSide::Bid,
                    qty: 10,
                    total: 1_020, // bid 102
                },
                LimitOrder {
                    account: "seat_alpha".to_string(),
                    side: OrderSide::Ask,
                    qty: 10,
                    total: 1_000, // ask 100
                },
            ],
            15,
        )
        .expect("Epoch 1 Batch #2 should finalize across 4-validator Simplex quorum");
    assert_eq!(epoch1_batch2.block_height, 2);
    assert_eq!(epoch1_batch2.post_total_cbdc_supply, 301_000);
    assert_eq!(epoch1_batch2.post_total_bond_supply, 125_000);

    // =========================================================================
    // 3. Mid-Flight `K-CARRY` (`"world-carry@1"`) Hot-Upgrade + 3-Phase ICAP DPR
    //    + Stale Pre-Upgrade Pin 1-Cycle `moved_pin_violation` Fallback
    // =========================================================================
    let upgrade_receipt = drex
        .execute_k_carry_hot_upgrade()
        .expect("mid-flight K-CARRY ('world-carry@1') + 3-phase ICAP DPR hot-swap should commit across quorum");

    assert_eq!(upgrade_receipt.from_epoch, 1);
    assert_eq!(upgrade_receipt.to_epoch, 2);
    assert_eq!(
        upgrade_receipt.from_law_pin_digest,
        drex.package.epoch1_law_pin_digest
    );
    assert_eq!(
        upgrade_receipt.to_law_pin_digest,
        drex.package.epoch2_law_pin_digest
    );
    assert_eq!(
        upgrade_receipt.carry_cert.named_drops,
        vec!["cell.legacy_epoch1_quote_scratch".to_string()]
    );
    assert_eq!(upgrade_receipt.carry_cert.post_total_supply, 301_000);
    assert_eq!(upgrade_receipt.finalized_block.height, 3);
    assert_eq!(upgrade_receipt.icap_swap_receipts.len(), 4);
    for (vid, swap) in upgrade_receipt.icap_swap_receipts.iter().enumerate() {
        assert!(
            swap.committed && !swap.fallback_activated && !swap.moved_pin_violation,
            "validator {vid} 3-phase ICAP DPR hot-swap must commit glitch-free"
        );
        assert_eq!(
            swap.held_output_port0_during_isolation, 700,
            "validator {vid} skid-buffer isolation fence must hold steady port0 == 700 during DPR"
        );
        assert_eq!(
            drex.host(vid).unwrap().active_law_pin_digest(),
            drex.package.epoch2_law_pin_digest
        );
        assert_eq!(drex.host(vid).unwrap().active_dpr_epoch_id(), 2);
    }

    // Negative test: stale pre-upgrade Epoch 1 pin triggers 1-cycle `moved_pin_violation` fallback
    let stale_fallback_receipt = drex
        .probe_stale_pre_upgrade_pin(0)
        .expect("stale pre-upgrade Epoch 1 pin must trigger 1-cycle SlotGuardReg fallback");
    assert!(!stale_fallback_receipt.committed);
    assert!(stale_fallback_receipt.fallback_activated);
    assert!(stale_fallback_receipt.moved_pin_violation);
    assert_eq!(
        stale_fallback_receipt.held_output_port0_during_isolation,
        700
    );
    // Active law pin on validator 0 remains locked to Epoch 2 after rejecting the stale pin
    assert_eq!(
        drex.host(0).unwrap().active_law_pin_digest(),
        drex.package.epoch2_law_pin_digest
    );

    // Finalize an Epoch 2 batch across all 4 validators under the upgraded law
    let epoch2_batch1 = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_treasury".to_string(),
                    side: OrderSide::Bid,
                    qty: 30,
                    total: 3_000,
                },
                LimitOrder {
                    account: "seat_alpha".to_string(),
                    side: OrderSide::Ask,
                    qty: 15,
                    total: 1_470,
                },
                LimitOrder {
                    account: "seat_gamma".to_string(),
                    side: OrderSide::Ask,
                    qty: 15,
                    total: 1_470,
                },
            ],
            10,
        )
        .expect("Epoch 2 Batch #1 should finalize under upgraded Epoch 2 law pin");

    assert_eq!(epoch2_batch1.carry_epoch, 2);
    assert_eq!(epoch2_batch1.block_height, 4);
    assert_eq!(
        epoch2_batch1.active_law_pin_digest,
        drex.package.epoch2_law_pin_digest
    );
    assert!(
        epoch2_batch1
            .witness_formats
            .contains(&"world-carry@1".to_string()),
        "Epoch 2 turn must carry 'world-carry@1' TurnJudgeWitness"
    );
    assert!(
        epoch2_batch1
            .witness_formats
            .contains(&"drex-clearing@1".to_string()),
        "Epoch 2 turn must carry 'drex-clearing@1' TurnJudgeWitness"
    );
    assert_eq!(epoch2_batch1.post_total_cbdc_supply, 301_000);
    assert_eq!(epoch2_batch1.post_total_bond_supply, 125_000);

    // =========================================================================
    // 4. Validator #3 Crash Mid-Epoch, 3-of-4 Live Quorum Finality, Durable WAL
    //    Recovery, Catch-Up, Supply Conservation & Zero Double-Execution
    // =========================================================================
    drex.crash_validator(3)
        .expect("crashing validator #3 should succeed");
    assert!(!drex.host(3).unwrap().is_memory_up());
    assert_eq!(drex.host(3).unwrap().committed_height(), 0);

    // Finalize two Epoch 2 batches on the remaining 3-of-4 quorum ({0, 1, 2}).
    // Note: height 4 was finalized at view 4 (leader = 3 before crash), and advancing through
    // subsequent views while validator #3 is down also tests 3-of-4 `SkipCert` view-skip when
    // `(view - 1) % 4 == 3`!
    let outage_batch1 = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_alpha".to_string(),
                    side: OrderSide::Bid,
                    qty: 12,
                    total: 1_200,
                },
                LimitOrder {
                    account: "seat_beta".to_string(),
                    side: OrderSide::Ask,
                    qty: 12,
                    total: 1_176,
                },
            ],
            20,
        )
        .expect("remaining 3-of-4 quorum should finalize outage_batch1 while validator #3 is down");
    assert_eq!(outage_batch1.block_height, 5);
    assert_eq!(outage_batch1.validator_telemetry.len(), 3);
    assert!(!outage_batch1.validator_telemetry.contains_key(&3));

    let outage_batch2 = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_gamma".to_string(),
                    side: OrderSide::Bid,
                    qty: 8,
                    total: 800,
                },
                LimitOrder {
                    account: "seat_treasury".to_string(),
                    side: OrderSide::Ask,
                    qty: 8,
                    total: 784,
                },
            ],
            15,
        )
        .expect("remaining 3-of-4 quorum should finalize outage_batch2 while validator #3 is down");
    assert_eq!(outage_batch2.block_height, 6);
    assert_eq!(outage_batch2.post_total_cbdc_supply, 301_000);
    assert_eq!(outage_batch2.post_total_bond_supply, 125_000);

    // Restart validator #3 from its durable WAL (`DurableSimplexHost::recover`) and catch up!
    let recovery = drex
        .recover_and_catch_up_validator(3)
        .expect("validator #3 should recover from WAL and catch up to finalized height 6 + Epoch 2 DPR");

    assert_eq!(recovery.validator_id, 3);
    assert_eq!(
        recovery.wal_restored_height, 4,
        "validator #3 durable WAL must restore heights 1..=4 committed prior to crash"
    );
    assert_eq!(
        recovery.wal_restored_dpr_epoch, 2,
        "validator #3 durable WAL must restore Epoch 2 DPR specialization slot prior to catch-up"
    );
    assert_eq!(
        recovery.missed_blocks_applied, 2,
        "validator #3 must apply strictly the 2 missed blocks (heights 5 and 6)"
    );
    assert_eq!(recovery.final_committed_height, 6);
    assert_eq!(recovery.final_dpr_epoch, 2);
    assert_eq!(
        recovery.final_law_pin_digest,
        drex.package.epoch2_law_pin_digest
    );
    assert!(
        recovery.unanimous_across_all_4_validators,
        "all 4 validators (V0..V3) must agree on height, state_root, DPR epoch, and law pin"
    );
    assert_eq!(recovery.conserved_total_cbdc_supply, 301_000);
    assert_eq!(recovery.conserved_total_bond_supply, 125_000);
    assert_eq!(
        recovery.idempotent_recatchup_blocks, 0,
        "re-running catch_up_validator(3) must apply 0 blocks (zero double-execution)"
    );
    assert!(
        recovery.double_expose_refused,
        "DurableNodeWal expose_once must refuse re-exposing any committed batch effect"
    );
    assert!(
        recovery.post_recovery_equivocation_refused,
        "DurableNodeWal must refuse conflicting votes in pre-crash views after recovery"
    );

    // Submit one more batch now that validator #3 is back online (forcing a view where validator #3
    // participates in the full 4-of-4 cluster)
    let post_recovery_batch = drex
        .submit_and_finalize_batch(
            vec![
                LimitOrder {
                    account: "seat_beta".to_string(),
                    side: OrderSide::Bid,
                    qty: 5,
                    total: 500,
                },
                LimitOrder {
                    account: "seat_alpha".to_string(),
                    side: OrderSide::Ask,
                    qty: 5,
                    total: 495,
                },
            ],
            5,
        )
        .expect("post-recovery 4-of-4 batch should finalize cleanly at height 7");
    assert_eq!(post_recovery_batch.block_height, 7);
    assert_eq!(post_recovery_batch.validator_telemetry.len(), 4);
    for vid in 0..4 {
        assert_eq!(drex.host(vid).unwrap().committed_height(), 7);
        assert_eq!(
            drex.host(vid).unwrap().state_root(),
            drex.host(0).unwrap().state_root()
        );
    }
}

#[test]
fn test_turn_judge_witness_fail_closed_refusal_across_proposal_vote_fastpath_and_commit() {
    let mut drex = SovereignDrexCluster::spawn_default()
        .expect("SovereignDrexCluster::spawn_default should succeed");

    // -------------------------------------------------------------------------
    // 1. Construct valid baseline witnesses for all 4 registered formats
    // -------------------------------------------------------------------------
    let orders = vec![
        LimitOrder {
            account: "seat_alpha".to_string(),
            side: OrderSide::Bid,
            qty: 10,
            total: 1_000,
        },
        LimitOrder {
            account: "seat_beta".to_string(),
            side: OrderSide::Ask,
            qty: 10,
            total: 980,
        },
    ];
    let cert = solve_primal_dual_clearing("CBDC", "BOND", 0, &orders).unwrap();
    let valid_drex_w = TurnJudgeWitness::drex_clearing(1, "CBDC", "BOND", 0, &orders, &cert);
    assert!(verify_turn_witness(&valid_drex_w).is_ok());

    // -------------------------------------------------------------------------
    // 2. Construct forged / corrupted witnesses across all required formats
    // -------------------------------------------------------------------------
    // (a) Unknown format_tag
    let unknown_format_w = TurnJudgeWitness {
        format_tag: "unregistered-judge@1".to_string(),
        grade: 1,
        object_payload: r#"{"query":1}"#.to_string(),
        cert_payload: r#"{"proof":1}"#.to_string(),
    };
    assert!(matches!(
        verify_turn_witness(&unknown_format_w),
        Err(JudgeWitnessError::UnknownFormatTag { .. })
    ));

    // (b) Malformed / unversioned format_tag
    let unversioned_w = TurnJudgeWitness {
        format_tag: "drex-clearing".to_string(),
        grade: 1,
        object_payload: valid_drex_w.object_payload.clone(),
        cert_payload: valid_drex_w.cert_payload.clone(),
    };
    assert!(matches!(
        verify_turn_witness(&unversioned_w),
        Err(JudgeWitnessError::InvalidFormatTag { .. })
    ));

    // (c) Empty `{}` JSON payload
    let empty_json_w = TurnJudgeWitness {
        format_tag: "drex-clearing@1".to_string(),
        grade: 1,
        object_payload: "{}".to_string(),
        cert_payload: "{}".to_string(),
    };
    assert!(matches!(
        verify_turn_witness(&empty_json_w),
        Err(JudgeWitnessError::EmptyOrTrivialPayload { .. })
    ));

    // (d) Malformed syntactic JSON
    let broken_json_w = TurnJudgeWitness {
        format_tag: "world-carry@1".to_string(),
        grade: 1,
        object_payload: "{broken_json".to_string(),
        cert_payload: r#"{"from_epoch":1}"#.to_string(),
    };
    assert!(matches!(
        verify_turn_witness(&broken_json_w),
        Err(JudgeWitnessError::MalformedJson { .. })
    ));

    // (e) Forged `"drex-clearing@1"` certificate (corrupted transfer amount breaking conservation)
    let mut forged_drex_cert = cert.clone();
    forged_drex_cert.transfers[0].amount += 500;
    let forged_drex_w =
        TurnJudgeWitness::drex_clearing(1, "CBDC", "BOND", 0, &orders, &forged_drex_cert);
    assert!(matches!(
        verify_turn_witness(&forged_drex_w),
        Err(JudgeWitnessError::CertificateRejected { .. })
    ));

    // (f) Forged `"world-carry@1"` certificate (dropping foreverCrown `"cell.treasury"`)
    let carry_obj = WorldCarryObject {
        epoch: 1,
        law_pin_digest: drex.package.epoch1_law_pin_digest,
        genesis_carry_hash: drex.package.genesis_carry_hash,
        cells: vec![WorldCarryCellSpec {
            name: "cell.treasury".to_string(),
            mandate_crown: "forever".to_string(),
            balance: 0,
            schema_ver: 1,
        }],
        seats: vec![],
        total_supply: 0,
    };
    let forged_carry_cert = WorldCarryCert {
        from_epoch: 1,
        target_epoch: 2,
        from_law_pin_digest: drex.package.epoch1_law_pin_digest,
        to_law_pin_digest: drex.package.epoch2_law_pin_digest,
        genesis_carry_hash: drex.package.genesis_carry_hash,
        kept_cells: vec![],
        named_drops: vec!["cell.treasury".to_string()], // Illegal drop of foreverCrown!
        rehydrated_refs: vec![],
        migrated_seats: vec![],
        post_total_supply: 0,
    };
    let forged_carry_w = TurnJudgeWitness::world_carry(1, &carry_obj, &forged_carry_cert);
    assert!(matches!(
        verify_turn_witness(&forged_carry_w),
        Err(JudgeWitnessError::CertificateRejected { .. })
    ));

    // (g) Forged `"interval@1"` certificate (claimed interval fails to enclose true range)
    let bad_iv_obj = IntervalWitnessObject {
        expr: IntervalExpr::Sqr {
            arg: Box::new(IntervalExpr::Var {
                name: "x".to_string(),
            }),
        },
        env: vec![IntervalVarBox {
            var: "x".to_string(),
            interval: RationalInterval::from_ints(0, 50),
        }],
        claimed_bound: RationalInterval::from_ints(0, 100), // 50^2 = 2500 > 100!
    };
    let forged_iv_w = TurnJudgeWitness::interval(1, &bad_iv_obj, &IntervalWitnessCert::Direct);
    assert!(matches!(
        verify_turn_witness(&forged_iv_w),
        Err(JudgeWitnessError::CertificateRejected { .. })
    ));

    // (h) Forged `"rtl-synth@1"` certificate (unsynchronized cross-clock-domain register < 2 stages)
    let rtl_obj = RtlSynthWitnessObject {
        module: "cdc_violation_mod".to_string(),
        primary_clock_domain: "clk_fast".to_string(),
        expected_input_count: 1,
        expected_output_count: 1,
    };
    let bad_rtl_cert = RtlSynthWitnessCert {
        module: "cdc_violation_mod".to_string(),
        clock_domain: "clk_fast".to_string(),
        inputs: vec!["in0".to_string()],
        wires: vec![RtlWireDecl {
            name: "slow_w0".to_string(),
            clock_domain: "clk_slow".to_string(),
            expr: RtlSignalRef::InPort { idx: 0 },
        }],
        regs: vec![RtlRegDecl {
            name: "bad_cdc_reg".to_string(),
            clock_domain: "clk_fast".to_string(),
            reset_val: 0,
            synchronizer_stages: 1, // < 2 stages across clk_slow -> clk_fast!
            next: RtlSignalRef::WireRef { idx: 0 },
        }],
        outputs: vec![RtlOutputDecl {
            name: "out0".to_string(),
            clock_domain: "clk_fast".to_string(),
            source: RtlSignalRef::RegRef { idx: 0 },
        }],
    };
    let forged_rtl_w = TurnJudgeWitness::rtl_synth(1, &rtl_obj, &bad_rtl_cert);
    assert!(matches!(
        verify_turn_witness(&forged_rtl_w),
        Err(JudgeWitnessError::CertificateRejected { .. })
    ));

    // -------------------------------------------------------------------------
    // 3. Prove Validators Refuse Forged Witnesses on Proposal, Fast-Path & Vote
    // -------------------------------------------------------------------------
    for bad_witness in [
        unknown_format_w,
        unversioned_w,
        empty_json_w,
        broken_json_w,
        forged_drex_w.clone(),
        forged_carry_w.clone(),
        forged_iv_w,
        forged_rtl_w,
    ] {
        let bad_turn = VaultTurn::new(
            cshake256_domain(
                b"obend.test.bad_turn",
                bad_witness.format_tag.as_bytes(),
                bad_witness.cert_payload.as_bytes(),
            ),
            "forged-agent",
            vec![],
            vec![(0x9999, vec![1, 2, 3])],
        )
        .with_witnesses(vec![bad_witness]);

        // Refused on `submit_turn` (Tier 1 Fast-Path & Tier 2 Simplex router entry)
        assert!(matches!(
            drex.cluster.submit_turn(bad_turn.clone()),
            Err(NodeError::InvalidTurnWitness(_))
        ));

        // Refused on `stage_contended_or_inflight_turn`
        assert!(matches!(
            drex.cluster.stage_contended_or_inflight_turn(bad_turn.clone()),
            Err(NodeError::InvalidTurnWitness(_))
        ));

        // Refused on `submit_concurrent_batch`
        assert!(matches!(
            drex.cluster.submit_concurrent_batch(vec![bad_turn]),
            Err(NodeError::InvalidTurnWitness(_))
        ));
    }

    // Refused on `perform_quorum_icap_dpr_upgrade_with_turn` when `"world-carry@1"` witness is forged
    let bad_upgrade_turn = VaultTurn::new(
        [0xEE; 32],
        "forged-k-carry",
        vec![],
        vec![(0x8888, vec![0xAA])],
    )
    .with_witnesses(vec![forged_carry_w]);
    assert!(matches!(
        drex.cluster.perform_quorum_icap_dpr_upgrade_with_turn(
            2,
            "forged_slot",
            drex.package.epoch2_law_pin_digest,
            bad_upgrade_turn,
            vec![],
        ),
        Err(NodeError::InvalidTurnWitness(_))
    ));

    // Also inject a signed `ConsensusNetMessage::Propose` and `FastPathPropose` carrying
    // `forged_drex_w` directly over the loopback network and verify peer validators reject the
    // wire frame (`rejected_wire_frames` increases) and cast zero Finalize votes / FastPathAcks!
    let pre_rejected_v1 = drex.cluster.nodes[1].rejected_wire_frames();
    let forged_net_turn = VaultTurn::new(
        [0x77; 32],
        "wire-forged-agent",
        vec![],
        vec![(0x7777, vec![9, 9])],
    )
    .with_witnesses(vec![forged_drex_w]);

    drex.cluster.nodes[0]
        .broadcast(ConsensusNetMessage::FastPathPropose(forged_net_turn.clone()))
        .unwrap();

    let forged_payload = obend_node::BlockPayload {
        height: 1,
        view: 1,
        turns: vec![forged_net_turn],
        drex_currency: "CBDC".to_string(),
        drex_goods: "BOND".to_string(),
        drex_epsilon: 0,
        drex_orders: vec![],
    };
    let forged_prop = PropCert::create(
        &drex.cluster.nodes[0].keypair,
        1,
        1,
        [0u8; 32],
        forged_payload.to_bytes(),
    );
    drex.cluster.nodes[0]
        .broadcast(ConsensusNetMessage::Propose(forged_prop, forged_payload))
        .unwrap();

    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    while drex.cluster.nodes[1].rejected_wire_frames() < pre_rejected_v1 + 2
        && std::time::Instant::now() < deadline
    {
        thread::sleep(Duration::from_millis(5));
    }

    assert!(
        drex.cluster.nodes[1].rejected_wire_frames() >= pre_rejected_v1 + 2,
        "peer validator #1 must reject both forged FastPathPropose and forged Propose wire frames"
    );
    assert_eq!(
        drex.cluster.nodes[1].committed_height(),
        0,
        "no block may be committed from a forged witness proposal"
    );
    assert!(
        drex.cluster.nodes[1].fast_path_certs().is_empty(),
        "no FastPathCert may be produced from a forged witness turn"
    );
}
