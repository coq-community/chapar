module Char =
struct

  include Char

  let is_lowercase c =
    'a' <= c && c <= 'z'

  let is_uppercase c =
    'A' <= c && c <= 'Z'

  let is_letter c =
    is_lowercase c || is_uppercase c

  let is_digit c =
    '0' <= c && c <= '9'

  let is_hex_digit c =
       ('0' <= c && c <= '9')
    || ('a' <= c && c <= 'f')
    || ('A' <= c && c <= 'F')

  let is_oct_digit c =
    ('0' <= c && c <= '7')

  let is_alphanum c =
    is_letter c || is_digit c

  let is_blank c =
    c = ' ' || c = '\t'

  let is_whitespace c =
    c = ' ' || c = '\t' || c = '\n' || c = '\r'

  let is_newline c =
    c = '\n' || c = '\r'

  let is_operator =
    String.contains "+-*/^<>=~#|&@$:?!\\"

end
