use obend_gui::evaluator::{NotebookCell, NotebookRunner};

#[test]
fn test_notebook_runner_execution() {
    let mut runner = NotebookRunner::new().expect("Init runner");
    let cells = vec![
        NotebookCell {
            id: "c1".to_string(),
            kind: "obendCode".to_string(),
            source: "let x = 1".to_string(),
            status: "ready".to_string(),
        },
        NotebookCell {
            id: "c2".to_string(),
            kind: "casSymbolic".to_string(),
            source: "x + y".to_string(),
            status: "ready".to_string(),
        },
    ];

    let results = runner.execute_cells(&cells);
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].0, "c1");
    assert!(results[0].1.is_ok());
    assert_eq!(results[1].0, "c2");
    assert!(results[1].1.is_ok());
}
