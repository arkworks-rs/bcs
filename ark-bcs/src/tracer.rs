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
                "[{}] at {}:{}:{}",
                description, self.file_name, self.line, self.column
            ))
        } else {
            f.write_fmt(format_args!(
                "[anonymous] at {}:{}:{}",
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

impl Default for TraceInfo {
    fn default() -> Self {
        Self {
            description: None,
            file_name: "Dummy",
            line: 0,
            column: 0,
        }
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
    use crate::tracer::TraceInfo;

    #[test]
    fn test_it_compiles() {
        let _tracer1 = iop_trace!();

        let _tracer2 = iop_trace!("some message title");
        #[cfg(feature = "std")]
        {
            eprintln!("tracer1: {}", _tracer1);
            eprintln!("tracer2: {}", _tracer2);
        }
    }

    const TRACE1: TraceInfo = iop_trace!();
    const TRACE2: TraceInfo = iop_trace!("some message title");
    const TRACE2_STR: &str = TRACE2.description();

    #[test]
    fn test_it_compilers_in_const() {
        #[cfg(feature = "std")]
        {
            eprintln!("tracer1: {}", TRACE1);
            eprintln!("tracer2: {}", TRACE2);
            eprintln!("tracer2 str: {}", TRACE2_STR);
        }
    }
}
