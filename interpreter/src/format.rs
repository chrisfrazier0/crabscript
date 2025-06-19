pub fn f64_to_string(value: f64) -> String {
  let s = value.to_string();
  if s.contains('.') {
    s
  } else {
    format!("{}.0", s)
  }
}
