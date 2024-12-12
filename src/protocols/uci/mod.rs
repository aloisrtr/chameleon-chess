//! # Universal Chess Interface
//! The Universal Chess Interface (UCI) protocol was designed by Rudolf Huber and
//! Stefan Meyer-Kahlen and is the most common protocol implement to communicate with
//! modern chess engines.
//!
//! ## Constraints and guarantees
//! - the implementation is **OS-independant**
//! - all communication is done **through standard I/O**
//! - when starting, the engine **waits for the server** (notably `isready` and `setoption` commands)
//! - the engine should **always be able to process standard input**, even during search
//! - all commands sent and received will **end with the newline character**
//! - the engine should never start searching or pondering without receiving a `go` command
//! - all `go` commands are preceded by a `position` command
//! - by default, book management should be done by the server
//! - the implementation should be **fault tolerant**, unexpected tokens or commands should be ignored
//!
//! ## Move format
//! UCI uses **long algebraic notation** for moves, i.e. `<from><to>[promotion]`.

use std::io::{BufRead, BufReader, BufWriter, Read, Write};

use self::commands::{UciCommand, UciMessage};

pub mod commands;

/// Represents a UCI compatible process that can be sent commands (a UCI client).
// pub struct UciClientEndpoint<'a> {
//     output: &'a dyn Write,
//     input: &'a dyn Read,
// }
// impl<'a> UciClientEndpoint<'a> {
//     // Creates a new client endpoint with the given input and output streams.
//     pub fn new(output: &'a dyn Write, input: &'a dyn Read) -> Self {
//         Self { output, input }
//     }
// }

/// Represents a UCI compatible process that can be sent messages (a UCI server).
pub struct UciServerEndpoint<I: Read, O: Write> {
    output: BufWriter<O>,
    input: BufReader<I>,
}
impl<I, O> UciServerEndpoint<I, O>
where
    I: Read,
    O: Write,
{
    // Creates a new server endpoint with the given input and output streams.
    pub fn new(output: O, input: I) -> Self {
        Self {
            output: BufWriter::new(output),
            input: BufReader::new(input),
        }
    }

    // Sends a given message to the UCI server.
    // # Errors
    pub fn send(&mut self, message: UciMessage) -> std::io::Result<()> {
        write!(self.output, "{message}");
        self.output.flush();
        Ok(())
    }

    // Tries to read a command from the UCI server.
    // # Errors
    pub fn read(&mut self) -> std::io::Result<Option<UciCommand>> {
        let mut buffer = String::new();
        self.input.read_line(&mut buffer)?;
        Ok(buffer.parse().ok())
    }
}
