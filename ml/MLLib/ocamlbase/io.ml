let input_lines chn =
  let lines = ref [] in
  let stop  = ref false in
    while not !stop do
      try lines := (input_line chn) :: !lines
      with End_of_file -> stop := true
    done;
    List.rev !lines

let input_all ?(block_size = 65536) chn =
  let buffer = String.create block_size in
  let result = Buffer.create 65536 in
  let chars_read = ref (-1) in
    while !chars_read <> 0 do
      chars_read := Pervasives.input chn buffer 0 block_size;
      Buffer.add_substring result buffer 0 !chars_read
    done;
    Buffer.contents result

let input chn buffer pos length =
  if 0 <= pos && pos + length <= String.length buffer then
    let chars_read = ref 0 in
    let stop       = ref false in
      while not !stop do
        let chars =
          Pervasives.input chn buffer
            (pos + !chars_read) (length - !chars_read)
        in
          if chars > 0 then chars_read := !chars_read + chars
          else stop := true
      done;
      !chars_read
  else
    invalid_arg "Io.input: invalid substring"
