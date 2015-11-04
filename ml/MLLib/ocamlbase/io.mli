(** Input and output functions. *)

val input_lines: in_channel -> string list
(** [input_lines chn] reads all remaining lines from the channel [chn] and
    returns a list of strings containing these lines without the newline
    character ['\n'] at the line ends.

    @raise Failure if the channel contains a line whose length exceeds
    [Sys.max_string_length]. *)

val input_all: ?block_size: int -> in_channel -> string
(** [input_all ?block_size chn] reads the remaining input from the channel
    [chn] and returns it as a string.  The input is read in blocks of
    [block_size] characters.

    @param block_size default: 65536 characters, valid range: [1 <= block_size
    <= Sys.max_string_length].

    @raise Failure if the length of the channel exceeds
    Sys.max_string_length. *)

val input: in_channel -> string -> int -> int -> int
(** [input chn buffer pos length] reads up to [length] characters from the
    channel [chn] and stores them in the string [buffer], starting at position
    [pos].  It returns the actual number of characters read.  A value less
    than [length] is only returned if there are less than [length] characters
    available from [chn] (the [input] function in the [Pervasives] module is
    allowed to read less than [length] characters if it "finds it convenient
    to do a partial read").

    @raise Invalid_argument if [pos] and [length] do not specify a valid
    substring of [buffer]. *)
