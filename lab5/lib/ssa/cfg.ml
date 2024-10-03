open Core

(* Nodes are associated with labels; they also contain the associated basic block. *)

module CFG = struct
  module Node = struct
    type t = string [@@deriving sexp, hash, equal, compare]
  end

  module Edge = struct
    type t = string [@@deriving compare, equal]

    let default = ""
  end

  module EdgePair = struct
    type t = string * string [@@deriving sexp, hash, equal, compare]
  end

  include Graph.Imperative.Digraph.ConcreteLabeled (Node) (Edge)
end

module Dot = Graph.Graphviz.Dot (struct
  include CFG (* use the graph module from above *)

  let edge_attributes (_, e, _) = [ `Label e; `Color 4711 ]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes _ = [ `Shape `Box ]
  let vertex_name (t : Node.t) = t
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)

module Dominator = Graph.Dominator.Make (CFG)
module Dfs = Graph.Traverse.Dfs (CFG)
module Bfs = Graph.Traverse.Bfs (CFG)
module Topo = Graph.Topological.Make (CFG)
