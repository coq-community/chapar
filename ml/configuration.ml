open Common

type node_info = { 
   ip: string;  
   port: int
(*    prog: program *)
}

module type Configuration = sig

   val net_info: (node_id * node_info) list

end

