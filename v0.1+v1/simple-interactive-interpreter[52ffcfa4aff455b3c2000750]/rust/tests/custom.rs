use simple_interactive_interpreter::Interpreter;

#[test]
fn function_args() {
    let mut interp = Interpreter::new();
    assert_eq!(interp.input("fn echo x => x"), Ok(None));
    assert_eq!(interp.input("fn avg x y => (x+y)/2"), Ok(None));
    assert_eq!(interp.input("avg echo 4 echo 2"), Ok(Some(3.0)))
}
