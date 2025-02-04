use rlox::chunk::Chunk;
use rlox::instr::Instr;
use rlox::span::Location;

fn main() {
    let mut chunk = Chunk::new();

    let constant = chunk.add_constant(1.2);
    let span = Location { line: 12, col: 4 };

    chunk.write_instr(Instr::Const(constant), span);
    chunk.write_instr(Instr::Return, span);

    chunk
        .disassemble("test chunk", &mut std::io::stdout())
        .unwrap();
}
