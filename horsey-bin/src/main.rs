/*
Horsey, a chess engine that doubles as a chess library.
Copyright (C) 2025 Rautureau Aloïs

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

use horsey::uci::uci_client;

// const HELP_STR: &str = r#"
//     Horsey chess engine
//     Aloïs Rautureau <thinkingrocks@proton.me>

//     USAGE:
//         horsey               Runs the engine in UCI mode

//     FLAGS:
//         -h, --help           Prints this message
// "#;

pub fn main() {
    env_logger::init();

    uci_client().unwrap()
}
