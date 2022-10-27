/- 
Graphs 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec11_type_classes

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true



open PROOFS

open PROOFS.STR






/-!
### Graphs

A simple graph is specified by the following data: 
1. A type `V` of vertices 
2. An irreflexive symmetric binary predicate (i.e. relation) `adj` on `V` describing which pairs of vertices are adjacent. In other words, for vertices `v₁` and `v₂`, the proposition `adj v₁ v₂` expresses the condition for adjecency. 

- We want `adj` to be symmetric which is to say if vertex `v₁` is adjacent to vertex `v₂` then `v₂` is also adjacent to `v₁`.  
- We want `adj` to be irreflexive which is to say we do not want to have loops. 

The relation 
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.


Given a type `V`, then `G : simple_graph V` is a simple graph defined over `V` with an adjacency relation `G.adj` between vertices of type V that is symmetric (G.sym) and irreflexive (G.noloop).
-/



@[ext]
structure simple_graph_str (V : Type) :=
(adj : V → V → Prop)
(symm : symmetric adj)
(noloop : irreflexive adj)


variable {X : Type}
variables {V : Type} (G : simple_graph_str V)



/- 
Define the __empty graph__ on a vertex type `V`, i.e. the graph with no edges on a given vertex type `V`.
 -/
def empty_graph_str (V : Type) : simple_graph_str V := 
{ 
  adj := sorry, 
  symm := by {sorry,}, 
  noloop := by {sorry,}, 
}




/- 
### Challenge : 
Define a graph structure on the type `bool` where the only edge is between `ff` and `tt`. 
-/







structure preorder_str (X : Type) := 
(rel : X → X → Prop)
(rflx : reflexive rel) 
(trns : transitive rel)


def preorder_bool : preorder_str bool := 
{
  rel := λ b, λ b', b && b' = b,
  rflx := by { unfold reflexive, -- 
               intro x, --   
               cases x, 
               repeat {refl}, 
               },
  trns := by { unfold transitive, 
               intros x y z, 
               intros h₁ h₂, rw ← h₁, rw bool_and_assoc, rw h₂}, 
}




/- 
### Challenge : 
Construct for any preorder a graph where there is an edge between any two points of the preorder if they are related to each other. 
-/
def graph_of_preorder_str  (X : Type) (ρ : preorder_str X) : simple_graph_str (X) := sorry 




/- 
### Challenge  : 
Construct the prodcut of two preorders. 
-/

def preorder_str.prod {X Y : Type} (P : preorder_str X) (Q : preorder_str Y) : 
preorder_str (X × Y) := 
{
  rel := λ a, λ b, (P.rel a.1 b.1) ∧ (Q.rel a.2 b.2), 
  rflx := by { sorry, },
  trns := by { sorry, },
}




/- 
### Challenge  : 
Construct the graph associated to the pointwise preorder on `bool × bool`. How many edges does this graph have?
-/

def graph_of_boolxbool_ptwise : simple_graph_str (bool × bool) := 
{ 
  adj := sorry,
  symm := sorry,
  noloop := sorry 
}





/-
### Challenge : 
Develope an API for simple graphs. 
-/


lemma adj_comm (u v : V) : 
  G.adj u v ↔ G.adj v u := 
begin
  sorry, 
end    





/-  
### Challenge : 
The __complete graph__ on a type `V` is the simple graph with all pairs of distinct vertices adjacent.  
-/



def complete_graph_str (V : Type) : simple_graph_str V := 
sorry 




/-
### Challenge : 
Define subgraphs. Suppose we have two graphs `G` and `H` on the same vertex type `V`. We say `G` is a subgraph of `H` if 
whenever any two vertex are connected by an edge in `G` they are connected by an edge in `H`. 
-/

def is_subgraph (G H : simple_graph_str V) : Prop := sorry 




/-
### Challenge : 
Show that the empty graph is a subgraph of any other graph. 
-/






/- ### Challenge :
Show that every graph is a subgraph of the complete graph on the same vertex type. 
-/ 









/-
### Challenge : 
Construct the sum of two graphs on the same type. The sum of two graphs `G` and `H` has an edge between two vertices if and only if either there is an edge between the same vertices in `G` or there is an edge between the same vertices in `H`. 
-/


def sum_of_graphs (G H : simple_graph_str V) : simple_graph_str V := 
{ adj := λ i j, G.adj i j ∨ H.adj i j,
  symm := sorry,
  noloop := sorry, }





/-
### Challenge : 
Define the __complement__ of a graph. The complement of a graph `G` is a graph `Gᶜ` on the same set of vertices as of G such that there will be an edge between two vertices `v₁` and `v₂` in G’, if and only if there is no edge in between `v₁` and `v₂` in `Gᶜ`.
-/

def complement (G : simple_graph_str V) : simple_graph_str V := 
{ adj := _,
  symm := _,
  noloop := _ }





/-
### Challenge : 
What is the sum of a graph of its complement. Prove it in Lean. 
-/




/- ### Challenge :
Define the embedding of graphs. A __graph embedding__ is a injective function `f`  between the vertex types of two such that for vertices `v₁ v₂ : V`,
`G.adj f(v₁) f(v₂) ↔ G.adj v₁ v₂ `. 
-/


structure graph_embedding {V W : Type} (G : simple_graph_str V) (H : simple_graph_str W) := 
(to_fun : V → W) 
(to_fun_inj : is_injective to_fun)
(embed : ∀ {a b : V}, H.adj (to_fun a) (to_fun b) ↔ G.adj a b)



/- ### Challenge :
Show that the relation `is_subgraph` defines an embedding structure. 
-/ 










