use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq, Clone)]
pub enum ObendError {
    #[error("Session initialization failed")]
    InitializationFailed,
    #[error("Null pointer provided to FFI boundary")]
    NullPointer,
    #[error("Invalid session handle")]
    InvalidSession,
    #[error("Decoding wire frame failed")]
    DecodeFailed,
    #[error("Cell evaluation failed")]
    EvalFailed,
    #[error("Turn proposal refused by contract or solvency check")]
    TurnRefused,
    #[error("Turn consensus commit failed")]
    CommitFailed,
    #[error("Read-only hardware projection adapter failed")]
    HardwareProjectionFailed,
    #[error("Receipt or Merkle proof invalid")]
    ReceiptInvalid,
    #[error("Lean runtime panic occurred")]
    Panic,
    #[error("Unknown error code {0}")]
    Unknown(i32),
    #[error("{0}: {1}")]
    WithDetail(Box<ObendError>, String),
}

impl ObendError {
    pub fn from_code(code: i32) -> Self {
        match code {
            0 => panic!("Attempted to convert success code 0 to ObendError"),
            -1 => Self::NullPointer,
            -2 => Self::InvalidSession,
            -3 => Self::DecodeFailed,
            -4 => Self::EvalFailed,
            -5 => Self::TurnRefused,
            -6 => Self::CommitFailed,
            -7 => Self::HardwareProjectionFailed,
            -8 => Self::ReceiptInvalid,
            -99 => Self::Panic,
            n => Self::Unknown(n),
        }
    }
}
