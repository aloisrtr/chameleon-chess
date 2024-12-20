use std::io::{BufRead, BufReader, BufWriter, Read, Write};

use super::commands::{UciCommand, UciError, UciMessage};

pub struct UciReader<I: Read> {
    inner: BufReader<I>,
}
impl<I: Read> UciReader<I> {
    // Creates a new UCI reader with the given input stream.
    pub fn new(input: I) -> Self {
        Self {
            inner: BufReader::new(input),
        }
    }

    /// Reads a command.
    pub fn read_command(&mut self) -> std::io::Result<Result<UciCommand, UciError>> {
        let mut buffer = String::new();
        self.inner.read_line(&mut buffer)?;
        Ok(buffer.parse())
    }
}

pub struct UciWriter<O: Write> {
    inner: BufWriter<O>,
}
impl<O: Write> UciWriter<O> {
    // Creates a new UCI writer with the given input stream.
    pub fn new(input: O) -> Self {
        Self {
            inner: BufWriter::new(input),
        }
    }

    /// Sends a message.
    pub fn send_message(&mut self, message: UciMessage) -> std::io::Result<()> {
        write!(self.inner, "{message}")?;
        self.inner.flush()
    }
}
