use ark_std::fmt::Display;
use std::fmt::Formatter;

#[derive(Clone, Copy)]
pub struct TraceInfo {
    pub(crate) description: Option<&'static str>,
    pub(crate) file_name: &'static str,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

impl Display for TraceInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

impl TraceInfo {
    pub fn new(
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
}

#[macro_export]
macro_rules! iop_trace {
    () => {{
        use $crate::tracer::*;
        TraceInfo::new(None, file!(), line!(), column!())
    }};
    ($description: expr) => {{
        use $crate::tracer::*;
        TraceInfo::new(
            Some($description),
            file!(),
            line!(),
            column!(),
        )
    }};
}

#[cfg(test)]
mod compile_tests {
    #[test]
    fn test_it_works() {
        let tracer1 = iop_trace!();

        let tracer2 = iop_trace!("some message title");
        eprintln!("tracer1: {}", tracer1);
        eprintln!("tracer2: {}", tracer2);
    }
}
