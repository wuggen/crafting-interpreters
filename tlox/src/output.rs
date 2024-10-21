//! Interpreter output streams.

use std::io::{self, Write};

pub enum OutputStream<'a> {
    Stdout,
    Stderr,
    With(Box<dyn Write + 'a>),
}

impl Default for OutputStream<'_> {
    fn default() -> Self {
        Self::Stdout
    }
}

impl OutputStream<'_> {
    pub fn with<'a, W: Write + 'a>(stream: W) -> OutputStream<'a> {
        OutputStream::With(Box::new(stream))
    }
}

impl Write for OutputStream<'_> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            OutputStream::Stdout => io::stdout().write(buf),
            OutputStream::Stderr => io::stderr().write(buf),
            OutputStream::With(write) => write.write(buf),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            OutputStream::Stdout => io::stdout().flush(),
            OutputStream::Stderr => io::stderr().flush(),
            OutputStream::With(write) => write.flush(),
        }
    }
}

pub struct OutputStreams<'a> {
    pub output: OutputStream<'a>,
    pub error: OutputStream<'a>,
}

impl Default for OutputStreams<'_> {
    fn default() -> Self {
        Self {
            output: OutputStream::Stdout,
            error: OutputStream::Stderr,
        }
    }
}

impl<'a> OutputStreams<'a> {
    pub fn new(output: OutputStream<'a>, error: OutputStream<'a>) -> Self {
        Self { output, error }
    }

    pub fn standard() -> Self {
        Self::default()
    }

    pub fn with_output<W: Write + 'a>(self, stream: W) -> Self {
        OutputStreams {
            output: OutputStream::with(stream),
            ..self
        }
    }

    pub fn with_error<W: Write + 'a>(self, stream: W) -> Self {
        OutputStreams {
            error: OutputStream::with(stream),
            ..self
        }
    }
}
