use rlox::chunk::Chunk;
use rlox::instr::Instr;
use rlox::session::Session;
use rlox::span::Location;

fn main() {
    let mut chunk = Chunk::new();

    let span = Location { line: 12, col: 4 };

    let constant = chunk.add_constant(1.2);
    chunk.write_instr(Instr::Const(constant), span);

    let constant = chunk.add_constant(3.4);
    chunk.write_instr(Instr::Const(constant), span);

    chunk.write_instr(Instr::Add, span);

    let constant = chunk.add_constant(5.6);
    chunk.write_instr(Instr::Const(constant), span);

    chunk.write_instr(Instr::Div, span);
    chunk.write_instr(Instr::Neg, span);

    chunk.write_instr(Instr::Ret, span);

    chunk
        .disassemble("test chunk", &mut std::io::stdout())
        .unwrap();

    let mut sess = Session::new();
    if rlox::config::VM_TRACE {
        eprintln!("\nExecution trace:");
    }
    sess.vm.evaluate(&chunk).unwrap();
}
