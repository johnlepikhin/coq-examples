
Require Import Arith.PeanoNat.

(* Запись STATE содержит поле server_id типа nat, не равное единице *)
Record STATE: Set :=
  {
    server_id : nat;
    cond1 : server_id <> 1;
  }.

(* Конструктор следующего server_id *)
Definition next_server_id (s : STATE) : nat :=
  match s.(server_id) with
  | 0 => 2                      (* Если у аргумента-STATE server_id=0, то генерируем 2 *)
  | _ => S s.(server_id)        (* Иначе генерируем server_id+1 *)
  end.

(* Доказательство корректности next_server_id *)
Theorem next_server_id_correct (s : STATE) : next_server_id s <> 1.
  unfold next_server_id.
  destruct s.(server_id).
  discriminate.
  cut (S n = 0 -> False).
  intro. 
  apply not_eq_S.
  exact H.
  apply PeanoNat.Nat.neq_succ_0.
Qed.

(* Конструктор STATE на основе уже существующего STATE *)
Definition next_state (s : STATE) : STATE := Build_STATE (next_server_id s) (next_server_id_correct s).

(* Доказательство корректности нулевого STATE *)
Theorem neq_succ_0 : 0 <> 1.
  trivial.
Qed.

(* Конструктор нулевого STATE *)
Definition initial_state := Build_STATE O neq_succ_0.
