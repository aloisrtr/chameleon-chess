//! # UCI options

use std::convert::Infallible;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum UciOptionAssignError {
    MismatchedTypes { expected: String, got: String },
    OutOfRange,
}
impl std::fmt::Display for UciOptionAssignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MismatchedTypes { expected, got } => {
                write!(f, "Mismatched types: expected {expected}, got {got}")
            }
            Self::OutOfRange => write!(f, "Value out of range"),
        }
    }
}
impl std::error::Error for UciOptionAssignError {}

/// The different types of UCI fields available.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciOptionField {
    Boolean {
        actual: bool,
        default: bool,
    },
    IntegerRange {
        actual: i32,
        default: i32,
        min: i32,
        max: i32,
    },
    Choice {
        default: usize,
        actual: usize,
        possibilities: Vec<String>,
    },
    String {
        default: String,
        actual: String,
    },
    Button,
}
impl UciOptionField {
    /// Returns the current value of this option field.
    pub fn value(&self) -> UciValue {
        match self {
            Self::Boolean { actual, .. } => UciValue::Boolean(*actual),
            Self::IntegerRange { actual, .. } => UciValue::Integer(*actual),
            Self::Choice {
                actual,
                possibilities,
                ..
            } => UciValue::Str(possibilities[*actual].clone()),
            Self::String { actual, .. } => UciValue::Str(actual.clone()),
            Self::Button => UciValue::Button,
        }
    }

    /// Assigns the given value to this option field.
    /// # Errors
    /// This function returns an error if the given value cannot be assigned to
    /// this field.
    pub fn assign(&mut self, value: UciValue) -> Result<(), UciOptionAssignError> {
        match self {
            Self::Boolean { actual, .. } => {
                if let UciValue::Boolean(value) = value {
                    *actual = value
                } else {
                    return Err(UciOptionAssignError::MismatchedTypes {
                        expected: "boolean".to_string(),
                        got: value.type_name().to_string(),
                    });
                }
            }
            Self::IntegerRange {
                actual, min, max, ..
            } => {
                if let UciValue::Integer(value) = value {
                    if (*min..=*max).contains(&value) {
                        *actual = value;
                    } else {
                        return Err(UciOptionAssignError::OutOfRange);
                    }
                } else {
                    return Err(UciOptionAssignError::MismatchedTypes {
                        expected: "integer".to_string(),
                        got: value.type_name().to_string(),
                    });
                }
            }
            Self::Choice {
                actual,
                possibilities,
                ..
            } => {
                if let UciValue::Str(value) = value {
                    if let Ok(value) = possibilities.binary_search(&value) {
                        *actual = value
                    } else {
                        return Err(UciOptionAssignError::OutOfRange);
                    }
                } else {
                    return Err(UciOptionAssignError::MismatchedTypes {
                        expected: "string".to_string(),
                        got: value.type_name().to_string(),
                    });
                }
            }
            Self::String { actual, .. } => {
                if let UciValue::Str(value) = value {
                    *actual = value
                } else {
                    return Err(UciOptionAssignError::MismatchedTypes {
                        expected: "string".into(),
                        got: value.type_name().into(),
                    });
                }
            }
            Self::Button => {
                todo!()
            }
        }
        Ok(())
    }
}

/// The different types of UCI values available.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciValue {
    Boolean(bool),
    Integer(i32),
    Str(String),
    Button,
}
impl UciValue {
    /// Returns a string indicating the type name of this value.
    pub fn type_name(&self) -> &str {
        match self {
            Self::Boolean(_) => "boolean",
            Self::Integer(_) => "integer",
            Self::Str(_) => "string",
            Self::Button => "button",
        }
    }
}
impl std::str::FromStr for UciValue {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(if let Ok(b) = s.parse::<bool>() {
            Self::Boolean(b)
        } else if let Ok(i) = s.parse::<i32>() {
            Self::Integer(i)
        } else if !s.is_empty() {
            Self::Str(String::from_str(s).unwrap())
        } else {
            Self::Button
        })
    }
}
