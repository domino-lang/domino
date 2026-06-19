
pub(super) fn logic_to_matrix(join: &str, list: &[String]) -> String {
    assert!(list.len() > 1);
    let trivial = list.join(join);
    if trivial.len() < 50 {
        trivial
    } else {
        let mut it = list.iter();
        let mut lines = vec![format!("\\phantom{{{}}}{}", join, it.next().unwrap())];
        let mut rest: Vec<_> = it.map(|s| format!("{join}{s}")).collect();
        lines.append(&mut rest);
        format!(
            "\\begin{{array}}{{c}}{}\\end{{array}}",
            lines.join("\\pclb")
        )
    }
}

pub(super) fn list_to_matrix(mut it: impl Iterator<Item=String>) -> String {
    let mut lines = Vec::new();
    let mut line = Vec::new();
    let mut len = 0;
    loop {
        // maybe this should be a minipage and latex figures linesbreaking ...
        match it.next() {
            None => {
                if !line.is_empty() {
                    lines.push(line.join(", "));
                }
                break;
            }
            Some(s) => {
                if len + s.len() > 30 {
                    line.push(String::new());
                    lines.push(line.join(", "));
                    line = Vec::new();
                    len = 0;
                }
                line.push(s.clone());
                len = len + std::cmp::max(6, s.len()) - 4 // latex makes string length and text length quite different
            }
        }
    }
    format!(
        "\\begin{{array}}{{c}}{}\\end{{array}}",
        lines.join("\\pclb")
    )
}
