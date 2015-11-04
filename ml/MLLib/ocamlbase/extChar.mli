(** Extended [Char] module.

    The [ExtChar] module contains an extension of the [Char] module in the
    OCaml standard library. *)

(** Extended [Char] module. *)
module Char:
sig

  val is_lowercase: char -> bool
  (** Returns [true] if the given character is an english lowercase letter. *)

  val is_uppercase: char -> bool
  (** Returns [true] if the given character is an english uppercase letter. *)

  val is_letter: char -> bool
  (** Returns [true] if the given character is an english letter. *)

  val is_digit: char -> bool
  (** Returns [true] if the given character is a decimal digit. *)

  val is_hex_digit: char -> bool
  (** Returns [true] if the given character is a hexadecimal digit. *)

  val is_oct_digit: char -> bool
  (** Returns [true] if the given character is an octal digit. *)

  val is_alphanum: char -> bool
  (** Returns [true] if the given character is a letter or a digit. *)

  val is_whitespace: char -> bool
  (** Returns [true] if the given character is a space, a tab or a newline (['
      '], ['\t'], ['\n'], or ['\r']). *)

  val is_blank: char -> bool
  (** Returns [true] if the given character is a space or a tab ([' '] or
      ['\t']). *)

  val is_newline: char -> bool
  (** Returns [true] if the given character is a newline (['\n'] or
      ['\r']). *)

  val is_operator: char -> bool
  (** Returns [true] if the given character is an operator character as
      defined in the OCaml language (i.e, one of ['+'], ['-'], ['*'], ['/'],
      ['^'] ['>'], ['<'], ['='], ['~'], ['#'], ['|'], ['&'], ['@'], ['$'],
      [':'] ['?'], ['!'], or ['\']). *)

  (** {2 From the OCaml standard library}

      The following definitions are unmodified from the OCaml standard
      library.  See the OCaml manual for documentation. *)

  val code : char -> int

  val chr : int -> char

  val escaped : char -> string

  val lowercase : char -> char

  val uppercase : char -> char

  type t = char

  val compare : t -> t -> int

end
