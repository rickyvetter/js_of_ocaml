open! Stdlib
open Code

val reverse_tree : (Addr.t, 'a) Hashtbl.t -> ('a, Code.Addr.Set.t) Hashtbl.t

val get_edges : (int, Code.Addr.Set.t) Hashtbl.t -> int -> Code.Addr.Set.t

type control_flow_graph =
  { succs : (int, Code.Addr.Set.t) Hashtbl.t
  ; preds : (int, Code.Addr.Set.t) Hashtbl.t
  ; reverse_post_order : int list
  ; block_order : (int, int) Hashtbl.t
  }

val is_backward : control_flow_graph -> int -> int -> bool

val is_forward : control_flow_graph -> int -> int -> bool

val build_graph : Code.block Code.Addr.Map.t -> int -> control_flow_graph

val dominator_tree : control_flow_graph -> (int, int) Hashtbl.t

val dominates : control_flow_graph -> (int, int) Hashtbl.t -> int -> int -> bool

val is_merge_node : control_flow_graph -> int -> bool

val is_loop_header : control_flow_graph -> int -> bool

val dominance_frontier :
  control_flow_graph -> (int, int) Hashtbl.t -> (int, Code.Addr.Set.t) Hashtbl.t
