mod response;

#[cfg(feature = "web")]
pub mod web;
#[cfg(feature = "web")]
pub use web::{Communicator, Error, ProverBackend, Result};

#[cfg(not(feature = "web"))]
pub mod process;
#[cfg(not(feature = "web"))]
pub use process::{Communicator, Error, ProverBackend, Result};

pub use response::ProverResponse;
