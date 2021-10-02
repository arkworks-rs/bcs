use ark_std::fmt::{Debug, Display, Formatter};

#[derive(Clone, Copy)]
#[allow(unused)]
/// Tracing information for IOP protocol code.
pub struct TraceInfo {
    pub(crate) description: Option<&'static str>,
    pub(crate) file_name: &'static str,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

impl Display for TraceInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> ark_std::fmt::Result {
        if let Some(description) = self.description {
            f.write_fmt(format_args!(
                "[{}]\n     at {}:{}:{}",
                description, self.file_name, self.line, self.column
            ))
        } else {
            f.write_fmt(format_args!(
                "[anonymous]\n     at {}:{}:{}",
                self.file_name, self.line, self.column
            ))
        }
    }
}

impl Debug for TraceInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> ark_std::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl TraceInfo {
    /// Returns a new `TraceInfo`. Note that this function should not be
    /// directly called. Instead, use `iop_trace!` instead.
    pub const fn new(
        description: Option<&'static str>,
        file_name: &'static str,
        line: u32,
        column: u32,
    ) -> Self {
        TraceInfo {
            description,
            file_name,
            line,
            column,
        }
    }

    /// Return a reference to the description of the trace. If None, return "".
    pub const fn description(&self) -> &str {
        match self.description {
            None => "",
            Some(s) => s,
        }
    }
}

#[macro_export]
/// Returns the tracing information at this point.
macro_rules! iop_trace {
    () => {{
        use $crate::tracer::*;
        TraceInfo::new(None, file!(), line!(), column!())
    }};
    ($description: expr) => {{
        use $crate::tracer::*;
        TraceInfo::new(Some($description), file!(), line!(), column!())
    }};
}

#[cfg(test)]
mod compile_tests {
    #[test]
    fn test_it_compiles() {
        let tracer1 = iop_trace!();

        let tracer2 = iop_trace!("some message title");
        eprintln!("tracer1: {}", tracer1);
        eprintln!("tracer2: {}", tracer2);
    }
}
