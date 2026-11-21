//! Conformance & fog-of-war non-interference tests for `obend-surfaces`.

use std::collections::{BTreeMap, BTreeSet};

use obend_surfaces::{
    apply_patch, diff, disclose, evaluate_affordance, format_value, project_view_node,
    synthesize_repair_badge, AffordanceStatus, BindFmt, CodecError, ContainerTag, CoordCell, Crumb,
    Disclosure, Disposition, Frustum, HaloHandle, HostStatus, MenuItem, PatchError, PillCase,
    ViewNode, ViewPatch, WorldState, MAX_VIEW_DEPTH,
};

fn all_25_variants() -> Vec<ViewNode> {
    vec![
        ViewNode::VStack(vec![ViewNode::Text("v".into())]),
        ViewNode::Row(vec![ViewNode::Divider]),
        ViewNode::Text("hello world".into()),
        ViewNode::Bind {
            slot: 3,
            label: "balance".into(),
            fmt: BindFmt::Amount,
            resolved: Some(1_234_567),
        },
        ViewNode::Button {
            label: "Submit".into(),
            turn: "vote".into(),
            arg: -7,
        },
        ViewNode::Input {
            bind_view: "draft_title".into(),
            fire_turn: "set_title".into(),
            submit_label: "Save".into(),
        },
        ViewNode::List(vec![ViewNode::Text("item 0".into())]),
        ViewNode::Table(vec![ViewNode::Row(vec![ViewNode::Text("cell".into())])]),
        ViewNode::Section {
            title: "Vault".into(),
            tag: "genuine".into(),
            children: vec![ViewNode::Divider],
        },
        ViewNode::Tabs {
            tabs: vec!["Inhabit".into(), "Inspect".into()],
            selected_slot: 1,
            select_turn: "select_tab".into(),
            resolved_active: Some(0),
            panels: vec![ViewNode::Text("p0".into()), ViewNode::Text("p1".into())],
        },
        ViewNode::Gauge {
            slot: 4,
            max: 100,
            label: "liveness".into(),
            resolved: Some(85),
        },
        ViewNode::Divider,
        ViewNode::Host {
            cell: "cell-alpha".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Text("hosted".into()))),
        },
        ViewNode::Grid {
            cols: 3,
            children: vec![ViewNode::Icon {
                glyph: "✦".into(),
                tag: "accent".into(),
            }],
        },
        ViewNode::Breadcrumb {
            items: vec![
                Crumb {
                    label: "Root".into(),
                    turn: "nav".into(),
                    arg: 0,
                },
                Crumb {
                    label: "Leaf".into(),
                    turn: String::new(),
                    arg: 1,
                },
            ],
        },
        ViewNode::Progress {
            value: 3,
            max: 5,
            label: "sync".into(),
        },
        ViewNode::Pill {
            text: "COMMIT".into(),
            tag: "warn".into(),
            slot: Some(2),
            cases: vec![
                PillCase {
                    value: 0,
                    label: "COMMIT".into(),
                    tag: "warn".into(),
                },
                PillCase {
                    value: 1,
                    label: "RESOLVED".into(),
                    tag: "good".into(),
                },
            ],
            resolved: Some(1),
        },
        ViewNode::Icon {
            glyph: "✓".into(),
            tag: "good".into(),
        },
        ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "Edit".into(),
                    turn: "edit_doc".into(),
                    arg: 1,
                    enabled: true,
                    wants_text: true,
                },
                MenuItem {
                    label: "Delete".into(),
                    turn: "del_doc".into(),
                    arg: 2,
                    enabled: false,
                    wants_text: false,
                },
            ],
        },
        ViewNode::Halo {
            target_slot: 9,
            handles: vec![HaloHandle {
                glyph: "⚙".into(),
                turn: "inspect".into(),
                arg: 9,
                enabled: true,
            }],
        },
        ViewNode::Slider {
            slot: 5,
            min: 0,
            max: 1000,
            turn: "seek".into(),
            resolved: Some(420),
        },
        ViewNode::Toggle {
            slot: 6,
            on_turn: "enable".into(),
            off_turn: "disable".into(),
            glyph_on: "✓".into(),
            glyph_off: "○".into(),
            label: "Cull".into(),
            resolved: Some(1),
        },
        ViewNode::Tile {
            handle: "svg-workbook-0".into(),
            w: 640,
            h: 480,
        },
        ViewNode::CoordGrid {
            cols: 2,
            cells: vec![
                CoordCell {
                    glyph: "♔".into(),
                    tag: "good".into(),
                    turn: "move".into(),
                    arg: 0,
                    highlight: true,
                },
                CoordCell {
                    glyph: "·".into(),
                    tag: "muted".into(),
                    turn: String::new(),
                    arg: 1,
                    highlight: false,
                },
            ],
        },
        ViewNode::Adept(Box::new(ViewNode::Text("raw-hash:0xdeadbeef".into()))),
    ]
}

#[test]
fn all_25_variants_dvn1_codec_and_limits() {
    let variants = all_25_variants();
    assert_eq!(variants.len(), 25);
    let mut tags = BTreeSet::new();
    for v in &variants {
        assert!(tags.insert(v.variant_tag()));
        let enc = v.encode().expect("encode");
        assert_eq!(ViewNode::decode(&enc).expect("decode"), *v);
    }
    assert_eq!(tags.len(), 25);

    let tree = ViewNode::VStack(variants);
    let mut bytes = tree.encode().expect("encode root");
    assert_eq!(ViewNode::decode(&bytes).expect("decode root"), tree);
    bytes.push(0);
    assert_eq!(ViewNode::decode(&bytes), Err(CodecError::TrailingBytes(1)));

    let mut deep = ViewNode::Divider;
    for _ in 0..=MAX_VIEW_DEPTH + 1 {
        deep = ViewNode::Adept(Box::new(deep));
    }
    assert!(matches!(deep.encode(), Err(CodecError::DepthExceeded(_))));
}

#[test]
fn diff_patch_roundtrip_and_mismatch_refusal() {
    let variants = all_25_variants();
    for (i, v) in variants.iter().enumerate() {
        assert_eq!(diff(v, v), ViewPatch::Keep);
        let next = &variants[(i + 5) % variants.len()];
        let p = diff(v, next);
        assert_eq!(apply_patch(v, &p), Ok(next.clone()));
    }
    assert_eq!(
        apply_patch(
            &ViewNode::Row(vec![ViewNode::Divider]),
            &ViewPatch::PatchContainer {
                tag: ContainerTag::VStack,
                patches: vec![ViewPatch::Keep],
            },
        ),
        Err(PatchError::ContainerMismatch)
    );
}

#[test]
fn frustum_fog_of_war_noninterference_and_nonvacuity() {
    let mut visible = BTreeSet::new();
    visible.insert(("root".to_owned(), 0usize));
    visible.insert(("shared".to_owned(), 1usize));
    visible.insert(("shared".to_owned(), 2usize));

    let mut allowed = BTreeSet::new();
    allowed.insert(("shared".to_owned(), 1usize));

    let mut policies = BTreeMap::new();
    policies.insert(
        "vault-secret".to_owned(),
        Disposition::Sever {
            snapshot_digest: 0xBEEF,
        },
    );
    policies.insert(
        "oracle".to_owned(),
        Disposition::Interpose {
            mock_label: "cached".into(),
        },
    );
    policies.insert(
        "shared".to_owned(),
        Disposition::Attenuate {
            allowed_slots: allowed,
        },
    );

    let frustum = Frustum {
        viewer: "alice".into(),
        visible_slots: visible,
        policies,
    };
    let tree = ViewNode::VStack(vec![
        ViewNode::Bind {
            slot: 0,
            label: "public".into(),
            fmt: BindFmt::Amount,
            resolved: None,
        },
        ViewNode::Host {
            cell: "vault-secret".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Bind {
                slot: 7,
                label: "secret".into(),
                fmt: BindFmt::Hex,
                resolved: None,
            })),
        },
        ViewNode::Host {
            cell: "shared".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Bind {
                slot: 2,
                label: "attenuated".into(),
                fmt: BindFmt::Raw,
                resolved: None,
            })),
        },
    ]);

    let mut w1 = WorldState::default();
    w1.set("root", 0, 1000);
    w1.set("vault-secret", 7, 42);
    w1.set("shared", 2, 111);

    let mut w2 = w1.clone();
    w2.set("vault-secret", 7, 999_999);
    w2.set("shared", 2, 888_888);

    let p1 = project_view_node(&frustum, &w1, "root", &tree);
    let p2 = project_view_node(&frustum, &w2, "root", &tree);
    assert_eq!(p1, p2);

    let mut w3 = w1;
    w3.set("root", 0, 2500);
    assert_ne!(p1, project_view_node(&frustum, &w3, "root", &tree));
}

#[test]
fn disclosure_format_and_repair_badges() {
    let tree = ViewNode::VStack(vec![
        ViewNode::Text("ok".into()),
        ViewNode::Adept(Box::new(ViewNode::Text("bones".into()))),
    ]);
    assert_eq!(
        disclose(&tree, Disclosure::Simple),
        ViewNode::VStack(vec![ViewNode::Text("ok".into())])
    );
    assert_eq!(format_value(1_234_567, BindFmt::Amount), "1,234,567");

    let req = vec!["cap.write".to_owned(), "cap.sign".to_owned()];
    let held = vec!["cap.write".to_owned()];
    let badge = synthesize_repair_badge("publish", &req, &held, true, None, "");
    assert_eq!(badge.missing_caps, vec!["cap.sign".to_owned()]);
    assert_eq!(
        evaluate_affordance("publish", &req, &req, true, None, ""),
        AffordanceStatus::Lit {
            turn: "publish".into()
        }
    );
}
