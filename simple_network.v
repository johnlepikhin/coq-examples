
(* Простая формализация сетевых соединений *)

Section Network.
  Require Import Relations_1.
  Variable NetworkNode : Prop.
  Variable HaveConnection : NetworkNode -> NetworkNode -> Prop.

  (* Соединения симметричны: когда есть соединение между N1 и N2, то есть и соединение между N2 и N1 *)
  Axiom ConnectionSymmetric : Symmetric NetworkNode HaveConnection.

  (* Соединения транзитивны: A--B, B--C -> A--C *)
  Axiom ConnectionTransitive : Transitive NetworkNode HaveConnection.

  (* Сеть рефлексивна: A--A (для любого A существует localhost) *)
  Axiom ConnectionReflexive : Reflexive NetworkNode HaveConnection.

  (* Доказательство транзитивности по 4 узлам: A--B, B--C, C--D -> A--D *)
  Lemma ConnectionTransitive4 : forall (a b c d : NetworkNode), HaveConnection a b -> HaveConnection b c -> HaveConnection c d -> HaveConnection a d.
    intros.
    cut (HaveConnection a c -> (HaveConnection a d)).
    intros.
    apply H2.
    cut (HaveConnection b c).
    cut (HaveConnection a b).
    apply ConnectionTransitive.
    auto.
    exact H0.
    intro.
    cut (HaveConnection c d).
    cut (HaveConnection a c).
    apply ConnectionTransitive.
    auto.
    exact H1.
  Qed.
End Network.
