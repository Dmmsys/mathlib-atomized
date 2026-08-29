/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Logic.Encodable.Pi

/-!
# Primitive recursive functions on Lists

The primitive recursive functions are defined in `Mathlib.Computability.Primrec.Basic`.
This file contains definitions and theorems about primitive recursive functions that
relate to operation on lists.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

@[expose] public section

open List (Vector)
open Denumerable Encodable Function


section

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open Primrec

set_option backward.privateInPublic true in
@[instance_reducible]
/--
Definition of `prim` / `prim` 的定义

English:
definition prim
  signature: : Primcodable (List β)
  body: ⟨H⟩

中文:
定义 prim
  签名: : Primcodable (列表 β)
  定义体: ⟨H⟩
-/
private def prim : Primcodable (List β) := ⟨H⟩

/--
theorem `list_casesOn'` / 定理 `list_casesOn'`

English:
theorem list_casesOn'
  statement: {f : α -> List β} {g : α -> σ} {h : α -> β × List β -> σ}
  proof: letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
to₂
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.

中文:
定理 list_casesOn'
  结论: {f : α -> 列表 β} {g : α -> σ} {h : α -> β × 列表 β -> σ}
  证明: letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
to₂
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.
-/
private theorem list_casesOn' {f : α -> List β} {g : α -> σ} {h : α -> β × List β -> σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
to₂
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      .id (encode_iff.2 hf)
option_some_iff.1 this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

set_option backward.privateInPublic true in
/--
theorem `list_foldl'` / 定理 `list_foldl'`

English:
theorem list_foldl'
  statement: {f : α -> List β} {g : α -> σ} {h : α -> σ × β -> σ}
  proof: by
  let := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd
to₂
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fu

中文:
定理 list_foldl'
  结论: {f : α -> 列表 β} {g : α -> σ} {h : α -> σ × β -> σ}
  证明: by
  let := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd
to₂
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fu
-/
private theorem list_foldl' {f : α -> List β} {g : α -> σ} {h : α -> σ × β -> σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  let := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd
to₂
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : Nat) => (G a)^[n] (g a, f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
nat_iterate (encode_iff.2 hf) (pair hg hf)
      hG)
  suffices forall a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this]; rw [List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero => rfl
  | succ n IH =>
    simp only [iterate_succ, comp_apply]
    rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

set_option backward.privateInPublic true in
/--
theorem `list_cons'` / 定理 `list_cons'`

English:
theorem list_cons'
  statement: (haveI := prim H; Primrec₂ (@List.cons β))
  proof: letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

中文:
定理 list_cons'
  结论: (haveI := prim H; Primrec₂ (@列表.cons β))
  证明: letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))
-/
private theorem list_cons' : (haveI := prim H; Primrec₂ (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

set_option backward.privateInPublic true in
/--
theorem `list_reverse'` / 定理 `list_reverse'`

English:
theorem list_reverse'
  proof: prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices forall l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction

中文:
定理 list_reverse'
  证明: prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices forall l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction
-/
private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices forall l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])

end

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
Instance `list` / 实例 `list`

English:
instance list
  signature: : Primcodable (List α)
  body: ⟨letI H := Primcodable.prim (List Nat)
    have : Primrec₂ fun (a : α) (o : Option (List Nat)) => o.map (List.cons (encode a)) :=
option_map snd (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List Nat) n).reverse.foldl
          

中文:
实例 list
  签名: : Primcodable (列表 α)
  定义体: ⟨letI H := Primcodable.prim (List Nat)
    have : Primrec₂ fun (a : α) (o : Option (List Nat)) => o.map (List.cons (encode a)) :=
option_map snd (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List Nat) n).reverse.foldl
          

Depends on / 依赖: List.cons, Primcodable, Primcodable.prim, Primrec, Primrec.comp, Primrec.encode, bind_decode_iff, decode, encode, fst.comp, list_cons, list_foldl, list_reverse, nat_i, o.map, option_map, reverse, reverse.foldl
-/
instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List Nat)
    have : Primrec₂ fun (a : α) (o : Option (List Nat)) => o.map (List.cons (encode a)) :=
option_map snd (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List Nat) n).reverse.foldl
          (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (.ofNat (List Nat))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| .swap this) Primrec₂.right)
nat_iff.1
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        rcases @decode α _ n.unpair.1 with - | a; · rfl
        simp only [Option.bind_some, Option.map_some]
        suffices forall (o : Option (List Nat)) (p), encode o = encode p ->
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p) from
          this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p
        · rfl
        · injection IH
        · injection IH
        · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/--
theorem `list_cons` / 定理 `list_cons`

English:
theorem list_cons
  statement: Primrec₂ (@List.cons α)
  proof: list_cons' (Primcodable.prim _)

中文:
定理 list_cons
  结论: Primrec₂ (@列表.cons α)
  证明: list_cons' (Primcodable.prim _)

Depends on / 依赖: Primcodable, Primcodable.prim, list_cons
-/
theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)

/--
theorem `list_casesOn` / 定理 `list_casesOn`

English:
theorem list_casesOn
  given: {f : α -> List β} {g : α -> σ} {h : α -> β × List β -> σ}
  proof: list_casesOn' (Primcodable.prim _)

中文:
定理 list_casesOn
  条件: {f : α -> 列表 β} {g : α -> σ} {h : α -> β × 列表 β -> σ}
  证明: list_casesOn' (Primcodable.prim _)

Depends on / 依赖: Primcodable, Primcodable.prim, list_casesOn
-/
theorem list_casesOn {f : α -> List β} {g : α -> σ} {h : α -> β × List β -> σ} :
    Primrec f ->
      Primrec g ->
        Primrec₂ h -> @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' (Primcodable.prim _)

/--
theorem `list_foldl` / 定理 `list_foldl`

English:
theorem list_foldl
  given: {f : α -> List β} {g : α -> σ} {h : α -> σ × β -> σ}
  proof: list_foldl' (Primcodable.prim _)

中文:
定理 list_foldl
  条件: {f : α -> 列表 β} {g : α -> σ} {h : α -> σ × β -> σ}
  证明: list_foldl' (Primcodable.prim _)

Depends on / 依赖: Primcodable, Primcodable.prim, list_foldl
-/
theorem list_foldl {f : α -> List β} {g : α -> σ} {h : α -> σ × β -> σ} :
    Primrec f ->
      Primrec g -> Primrec₂ h -> Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)

/--
theorem `list_reverse` / 定理 `list_reverse`

English:
theorem list_reverse
  statement: Primrec (@List.reverse α)
  proof: list_reverse' (Primcodable.prim _)

中文:
定理 list_reverse
  结论: Primrec (@列表.reverse α)
  证明: list_reverse' (Primcodable.prim _)

Depends on / 依赖: Primcodable, Primcodable.prim, list_reverse
-/
theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)

/--
theorem `list_foldr` / 定理 `list_foldr`

English:
theorem list_foldr
  statement: {f : α -> List β} {g : α -> σ} {h : α -> β × σ -> σ} (hf : Primrec f)
  proof: (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

中文:
定理 list_foldr
  结论: {f : α -> 列表 β} {g : α -> σ} {h : α -> β × σ -> σ} (hf : Primrec f)
  证明: (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

Depends on / 依赖: List.foldl_reverse, foldl_reverse, hh.comp, list_foldl, list_reverse, list_reverse.comp, of_eq
-/
theorem list_foldr {f : α -> List β} {g : α -> σ} {h : α -> β × σ -> σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

/--
theorem `list_head?` / 定理 `list_head?`

English:
theorem list_head?
  statement: Primrec (@List.head? α)
  proof: (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

中文:
定理 list_head?
  结论: Primrec (@列表.head? α)
  证明: (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

Depends on / 依赖: fst.comp, list_casesOn, of_eq, option_some_iff
-/
theorem list_head? : Primrec (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

/--
theorem `list_headI` / 定理 `list_headI`

English:
theorem list_headI
  given: [Inhabited α]
  statement: Primrec (@List.headI α _)
  proof: (option_getD_default.comp list_head?).of_eq fun l => l.head!_eq_head?_getD.symm

中文:
定理 list_headI
  条件: [可居 α]
  结论: Primrec (@列表.headI α _)
  证明: (option_getD_default.comp list_head?).of_eq fun l => l.head!_eq_head?_getD.symm

Depends on / 依赖: _eq_head, _getD, _getD.symm, l.head, list_head, of_eq, option_getD_default, option_getD_default.comp
-/
theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_getD_default.comp list_head?).of_eq fun l => l.head!_eq_head?_getD.symm

/--
theorem `list_tail` / 定理 `list_tail`

English:
theorem list_tail
  statement: Primrec (@List.tail α)
  proof: (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

中文:
定理 list_tail
  结论: Primrec (@列表.tail α)
  证明: (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

Depends on / 依赖: list_casesOn, of_eq, snd.comp
-/
theorem list_tail : Primrec (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

/--
theorem `list_rec` / 定理 `list_rec`

English:
theorem list_rec
  statement: {f : α -> List β} {g : α -> σ} {h : α -> β × List β × σ -> σ} (hf : Primrec f)
  proof: let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
list_foldr hf (pair (const []) hg)
to₂ pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun 

中文:
定理 list_rec
  结论: {f : α -> 列表 β} {g : α -> σ} {h : α -> β × 列表 β × σ -> σ} (hf : Primrec f)
  证明: let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
list_foldr hf (pair (const []) hg)
to₂ pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun 

Depends on / 依赖: List.recOn, Primrec, fst.comp, list_cons, list_cons.comp, list_foldr, of_eq, snd.comp
-/
theorem list_rec {f : α -> List β} {g : α -> σ} {h : α -> β × List β × σ -> σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
list_foldr hf (pair (const []) hg)
to₂ pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction f a <;> simp [*]

/--
theorem `list_getElem?` / 定理 `list_getElem?`

English:
theorem list_getElem?
  statement: Primrec₂ ((·[·]? : List α -> Nat -> Option α))
  proof: let F (l : List α) (n : Nat) :=
    l.foldl
      (fun (s : Nat oplus α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => Nat oplus α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (su

中文:
定理 list_getElem?
  结论: Primrec₂ ((·[·]? : 列表 α -> 自然数 -> 选项类型 α))
  证明: let F (l : List α) (n : Nat) :=
    l.foldl
      (fun (s : Nat oplus α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => Nat oplus α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (su

Depends on / 依赖: Nat.casesOn, Primrec, Sum.casesOn, Sum.inl, Sum.inr, casesOn, l.foldl, list_foldl, nat_casesOn, snd.comp, sumCasesOn, sumInl, sumInl.comp, sumInr, sumInr.comp
-/
theorem list_getElem? : Primrec₂ ((·[·]? : List α -> Nat -> Option α)) :=
  let F (l : List α) (n : Nat) :=
    l.foldl
      (fun (s : Nat oplus α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => Nat oplus α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (sumInr.comp <| snd.comp fst) (sumInl.comp snd).to₂).to₂
              (sumInr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × Nat => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sumCasesOn hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction l generalizing n with
    | nil => rfl
    | cons a l IH =>
      rcases n with - | n
      · dsimp [F]
        clear IH
        induction l <;> simp_all
      · simpa using! IH ..

/--
theorem `list_getD` / 定理 `list_getD`

English:
theorem list_getD
  given: (d : α)
  statement: Primrec₂ fun l n => List.getD l n d
  proof: by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

中文:
定理 list_getD
  条件: (d : α)
  结论: Primrec₂ fun l n => 列表.getD l n d
  证明: by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

Depends on / 依赖: List.getD_eq_getElem, _getD, getD_eq_getElem, list_getElem, option_getD, option_getD.comp
-/
theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

/--
theorem `list_getI` / 定理 `list_getI`

English:
theorem list_getI
  given: [Inhabited α]
  statement: Primrec₂ (@List.getI α _)
  proof: list_getD _

中文:
定理 list_getI
  条件: [可居 α]
  结论: Primrec₂ (@列表.getI α _)
  证明: list_getD _

Depends on / 依赖: list_getD
-/
theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _

/--
theorem `list_append` / 定理 `list_append`

English:
theorem list_append
  statement: Primrec₂ ((· ++ ·) : List α -> List α -> List α)
  proof: (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

中文:
定理 list_append
  结论: Primrec₂ ((· ++ ·) : 列表 α -> 列表 α -> 列表 α)
  证明: (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

Depends on / 依赖: list_cons, list_foldr, of_eq
-/
theorem list_append : Primrec₂ ((· ++ ·) : List α -> List α -> List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

/--
theorem `list_concat` / 定理 `list_concat`

English:
theorem list_concat
  statement: Primrec₂ fun l (a : α) => l ++ [a]
  proof: list_append.comp fst (list_cons.comp snd (const []))

中文:
定理 list_concat
  结论: Primrec₂ fun l (a : α) => l ++ [a]
  证明: list_append.comp fst (list_cons.comp snd (const []))

Depends on / 依赖: list_append, list_append.comp, list_cons, list_cons.comp
-/
theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))

/--
theorem `list_map` / 定理 `list_map`

English:
theorem list_map
  given: {f : α -> List β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g)
  proof: (list_foldr hf (const []) <|
to₂ list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

中文:
定理 list_map
  条件: {f : α -> 列表 β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g)
  证明: (list_foldr hf (const []) <|
to₂ list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

Depends on / 依赖: fst.comp, hg.comp, list_cons, list_cons.comp, list_foldr, of_eq, snd.comp
-/
theorem list_map {f : α -> List β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
to₂ list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

/--
theorem `list_range` / 定理 `list_range`

English:
theorem list_range
  statement: Primrec List.range
  proof: (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

中文:
定理 list_range
  结论: Primrec 列表.range
  证明: (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

Depends on / 依赖: List.range_succ, list_concat, list_concat.comp, nat_rec, of_eq, range_succ
-/
theorem list_range : Primrec List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

/--
theorem `list_flatten` / 定理 `list_flatten`

English:
theorem list_flatten
  statement: Primrec (@List.flatten α)
  proof: (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

中文:
定理 list_flatten
  结论: Primrec (@列表.flatten α)
  证明: (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

Depends on / 依赖: list_append, list_foldr, of_eq
-/
theorem list_flatten : Primrec (@List.flatten α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

/--
theorem `list_flatMap` / 定理 `list_flatMap`

English:
theorem list_flatMap
  given: {f : α -> List β} {g : α -> β -> List σ} (hf : Primrec f) (hg : Primrec₂ g)
  proof: list_flatten.comp (list_map hf hg)

中文:
定理 list_flatMap
  条件: {f : α -> 列表 β} {g : α -> β -> 列表 σ} (hf : Primrec f) (hg : Primrec₂ g)
  证明: list_flatten.comp (list_map hf hg)

Depends on / 依赖: list_flatten, list_flatten.comp, list_map
-/
theorem list_flatMap {f : α -> List β} {g : α -> β -> List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

/--
theorem `optionToList` / 定理 `optionToList`

English:
theorem optionToList
  statement: Primrec (Option.toList : Option α -> List α)
  proof: (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

中文:
定理 optionToList
  结论: Primrec (选项类型.toList : 选项类型 α -> 列表 α)
  证明: (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

Depends on / 依赖: Primrec, Primrec.id, list_cons, list_cons.comp, of_eq, option_casesOn
-/
theorem optionToList : Primrec (Option.toList : Option α -> List α) :=
  (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

/--
theorem `listFilterMap` / 定理 `listFilterMap`

English:
theorem listFilterMap
  statement: {f : α -> List β} {g : α -> β -> Option σ}
  proof: (list_flatMap hf (comp₂ optionToList hg)).of_eq
fun _ => Eq.symm List.filterMap_eq_flatMap_toList _ _

中文:
定理 listFilterMap
  结论: {f : α -> 列表 β} {g : α -> β -> 选项类型 σ}
  证明: (list_flatMap hf (comp₂ optionToList hg)).of_eq
fun _ => Eq.symm List.filterMap_eq_flatMap_toList _ _

Depends on / 依赖: Eq.symm, List.filterMap_eq_flatMap_toList, filterMap_eq_flatMap_toList, list_flatMap, of_eq, optionToList
-/
theorem listFilterMap {f : α -> List β} {g : α -> β -> Option σ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
fun _ => Eq.symm List.filterMap_eq_flatMap_toList _ _

variable {p : α -> Prop} [DecidablePred p]

/--
theorem `list_length` / 定理 `list_length`

English:
theorem list_length
  statement: Primrec (@List.length α)
  proof: (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

中文:
定理 list_length
  结论: Primrec (@列表.length α)
  证明: (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

Depends on / 依赖: Primrec, Primrec.id, list_foldr, map_smul, of_eq, singleAddHom, snd.comp, succ.comp
-/
theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

/--
theorem `listFilter` / 定理 `listFilter`

English:
theorem listFilter
  given: (hf : PrimrecPred p)
  statement: Primrec fun L => List.filter (p ·) L
  proof: by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

中文:
定理 listFilter
  条件: (hf : PrimrecPred p)
  结论: Primrec fun L => 列表.filter (p ·) L
  证明: by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

Depends on / 依赖: List.filterMap_eq_filter, Option.guard, decide_eq_true_eq, filterMap_eq_filter, hf.comp, listFilterMap, option_some_iff, option_some_iff.mpr
-/
theorem listFilter (hf : PrimrecPred p) : Primrec fun L => List.filter (p ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

/--
theorem `list_findIdx` / 定理 `list_findIdx`

English:
theorem list_findIdx
  statement: {f : α -> List β} {p : α -> β -> Bool}
  proof: (list_foldr hf (const 0) <|
to₂ cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

中文:
定理 list_findIdx
  结论: {f : α -> 列表 β} {p : α -> β -> 布尔值}
  证明: (list_foldr hf (const 0) <|
to₂ cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

Depends on / 依赖: List.findIdx_cons, findIdx_cons, fst.comp, hp.comp, list_foldr, of_eq, snd.comp, succ.comp
-/
theorem list_findIdx {f : α -> List β} {p : α -> β -> Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
to₂ cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

/--
theorem `list_idxOf` / 定理 `list_idxOf`

English:
theorem list_idxOf
  given: [DecidableEq α]
  statement: Primrec₂ (@List.idxOf α _)
  proof: to₂ list_findIdx snd Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂

中文:
定理 list_idxOf
  条件: [DecidableEq α]
  结论: Primrec₂ (@列表.idxOf α _)
  证明: to₂ list_findIdx snd Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂

Depends on / 依赖: Primrec, Primrec.beq.comp, fst.comp, list_findIdx, snd.to
-/
theorem list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _) :=
to₂ list_findIdx snd Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂

/--
theorem `nat_strong_rec` / 定理 `nat_strong_rec`

English:
theorem nat_strong_rec
  statement: (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Primrec₂ g)
  proof: suffices Primrec₂ fun a n => (List.range n).map (f a) from
Primrec₂.option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
Primrec₂.option_some_iff.1
    (nat_rec (const (some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
       

中文:
定理 nat_strong_rec
  结论: (f : α -> 自然数 -> σ) {g : α -> 列表 σ -> 选项类型 σ} (hg : Primrec₂ g)
  证明: suffices Primrec₂ fun a n => (List.range n).map (f a) from
Primrec₂.option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
Primrec₂.option_some_iff.1
    (nat_rec (const (some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
       

Depends on / 依赖: List.range, List.range_succ, fst.comp, hg.comp, list_concat, list_concat.comp, list_getElem, nat_rec, of_eq, option_bind, option_map, option_some_iff, range_succ, snd.comp, succ.comp, this.comp
-/
theorem nat_strong_rec (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Primrec₂ g)
    (H : forall a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
Primrec₂.option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
Primrec₂.option_some_iff.1
    (nat_rec (const (some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `listLookup` / 定理 `listLookup`

English:
theorem listLookup
  given: [DecidableEq α]
  statement: Primrec₂ (List.lookup : α -> List (α × β) -> Option β)
  proof: (to₂ <| list_rec snd (const none) <|
to₂
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : 

中文:
定理 listLookup
  条件: [DecidableEq α]
  结论: Primrec₂ (列表.lookup : α -> 列表 (α × β) -> 选项类型 β)
  证明: (to₂ <| list_rec snd (const none) <|
to₂
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : 

Depends on / 依赖: List.lookup, Primrec, Primrec.beq.comp, fst.comp, list_rec, lookup, of_eq, option_some, option_some.comp, snd.comp
-/
theorem listLookup [DecidableEq α] : Primrec₂ (List.lookup : α -> List (α × β) -> Option β) :=
  (to₂ <| list_rec snd (const none) <|
to₂
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : a == p.1 <;> simp

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `nat_omega_rec'` / 定理 `nat_omega_rec'`

English:
theorem nat_omega_rec'
  statement: (f : β -> σ) {m : β -> Nat} {l : β -> List β} {g : β -> List σ -> Option σ}
  proof: by
  have : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : Nat -> List β := fun n => n.rec [b] fun _ bs => bs.flatMap l
  let graph (b : β) : Nat -> List (β × σ) := fun 

中文:
定理 nat_omega_rec'
  结论: (f : β -> σ) {m : β -> 自然数} {l : β -> 列表 β} {g : β -> 列表 σ -> 选项类型 σ}
  证明: by
  have : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : Nat -> List β := fun n => n.rec [b] fun _ bs => bs.flatMap l
  let graph (b : β) : Nat -> List (β × σ) := fun 

Depends on / 依赖: DecidableEq, Encodable, Encodable.decidableEqOfEncodable, M.lookup, Option.toList, bindList, bs.flatMap, decidableEqOfEncodable, filterMap, flatMap, i.rec, listLookup, listLookup.co, list_flatMap, lookup, mapGraph, mapGraph_primrec, n.rec, optionToList, optionToList.comp
-/
theorem nat_omega_rec' (f : β -> σ) {m : β -> Nat} {l : β -> List β} {g : β -> List σ -> Option σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
    (Ord : forall b, forall b' in l b, m b' < m b)
    (H : forall b, g b ((l b).map f) = some (f b)) : Primrec f := by
  have : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : Nat -> List β := fun n => n.rec [b] fun _ bs => bs.flatMap l
  let graph (b : β) : Nat -> List (β × σ) := fun i => i.rec [] fun i ih =>
    (bindList b (m b - i)).filterMap fun b' => (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : Primrec₂ mapGraph :=
to₂ list_flatMap snd optionToList.comp₂ listLookup.comp₂ .right (fst.comp₂ .left)
  have bindList_primrec : Primrec₂ (bindList) :=
    nat_rec' snd
      (list_cons.comp fst (const []))
      (to₂ <| list_flatMap (snd.comp snd) (hl.comp₂ .right))
  have graph_primrec : Primrec₂ (graph) :=
to₂ nat_rec' snd (const [])
to₂ listFilterMap
        (bindList_primrec.comp
          (fst.comp fst)
          (nat_sub.comp (hm.comp <| fst.comp fst) (fst.comp snd))) <|
to₂ option_map
              (hg.comp snd (mapGraph_primrec.comp (snd.comp <| snd.comp fst) (hl.comp snd)))
              (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right)
  have : Primrec (fun b => (graph b (m b + 1))[0]?.map Prod.snd) :=
    option_map (list_getElem?.comp (graph_primrec.comp Primrec.id (succ.comp hm)) (const 0))
      (snd.comp₂ Primrec₂.right)
exact option_some_iff.mp this.of_eq fun b => by
    have graph_eq_map_bindList (i : Nat) (hi : i <= m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x => (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : Nat) : forall b' in bindList b k, m b' < m b + 1 - k := by
          induction k with simp [bindList]
          | succ k ih =>
            grind
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' subseteq bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction bs' with simp [mapGraph]
        | cons b bs' ih =>
          have : b in bs ∧ bs' subseteq bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : forall i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : forall i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
      induction i with
      | zero => symm; simpa [graph] using bindList_eq_nil
      | succ i ih =>
        simp only [graph_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.le_of_lt_succ hi),
          Nat.succ_eq_add_one, bindList_succ, Nat.reduceSubDiff]
        apply List.filterMap_eq_map_iff_forall_eq_some.mpr
        intro b' ha'; simp; rw [mapGraph_graph]
        · exact H b'
        · exact (List.infix_flatMap_of_mem ha' l).subset
    simp [graph_eq_map_bindList (m b + 1) (Nat.le_refl _), bindList]

/--
theorem `nat_omega_rec` / 定理 `nat_omega_rec`

English:
theorem nat_omega_rec
  statement: (f : α -> β -> σ) {m : α -> β -> Nat}
  proof: Primrec₂.uncurry.mp
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using! Ord) (by simpa [Funct

中文:
定理 nat_omega_rec
  结论: (f : α -> β -> σ) {m : α -> β -> 自然数}
  证明: Primrec₂.uncurry.mp
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using! Ord) (by simpa [Funct

Depends on / 依赖: Function, Function.comp, Function.uncurry, fst.comp, hg.comp, hl.comp, list_map, nat_omega_rec, pair.comp, snd.comp, uncurry, uncurry.mp, uncurry.mpr
-/
theorem nat_omega_rec (f : α -> β -> σ) {m : α -> β -> Nat}
    {l : α -> β -> List β} {g : α -> β × List σ -> Option σ}
    (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Primrec₂ g)
    (Ord : forall a b, forall b' in l a b, m a b' < m a b)
    (H : forall a b, g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f :=
Primrec₂.uncurry.mp
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using! Ord) (by simpa [Function.comp] using! H)

/--
theorem `list_drop` / 定理 `list_drop`

English:
theorem list_drop
  statement: Primrec₂ (List.drop : Nat -> List α -> List α)
  proof: (nat_iterate fst snd (list_tail.comp₂ .right)).to₂.of_eq fun n l => l.tail_iterate n

中文:
定理 list_drop
  结论: Primrec₂ (列表.drop : 自然数 -> 列表 α -> 列表 α)
  证明: (nat_iterate fst snd (list_tail.comp₂ .right)).to₂.of_eq fun n l => l.tail_iterate n

Depends on / 依赖: l.tail_iterate, list_tail, list_tail.comp, nat_iterate, of_eq, tail_iterate
-/
theorem list_drop : Primrec₂ (List.drop : Nat -> List α -> List α) :=
  (nat_iterate fst snd (list_tail.comp₂ .right)).to₂.of_eq fun n l => l.tail_iterate n

/--
theorem `list_take` / 定理 `list_take`

English:
theorem list_take
  statement: Primrec₂ (List.take : Nat -> List α -> List α)
  proof: (list_reverse.comp (list_drop.comp (nat_sub.comp (list_length.comp snd) fst)
    (list_reverse.comp snd))).of_eq fun ⟨n, l⟩ => by
    rw [← List.reverse_reverse (l.take n)]; rw [List.reverse_take]

中文:
定理 list_take
  结论: Primrec₂ (列表.take : 自然数 -> 列表 α -> 列表 α)
  证明: (list_reverse.comp (list_drop.comp (nat_sub.comp (list_length.comp snd) fst)
    (list_reverse.comp snd))).of_eq fun ⟨n, l⟩ => by
    rw [← List.reverse_reverse (l.take n)]; rw [List.reverse_take]

Depends on / 依赖: List.reverse_reverse, List.reverse_take, l.take, list_drop, list_drop.comp, list_length, list_length.comp, list_reverse, list_reverse.comp, nat_sub, nat_sub.comp, of_eq, reverse_reverse, reverse_take
-/
theorem list_take : Primrec₂ (List.take : Nat -> List α -> List α) :=
  (list_reverse.comp (list_drop.comp (nat_sub.comp (list_length.comp snd) fst)
    (list_reverse.comp snd))).of_eq fun ⟨n, l⟩ => by
    rw [← List.reverse_reverse (l.take n)]; rw [List.reverse_take]

/--
theorem `list_takeWhile` / 定理 `list_takeWhile`

English:
theorem list_takeWhile
  given: {p : α -> Bool} (hp : Primrec p)
  statement: Primrec (List.takeWhile p)
  proof: (list_take.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.takeWhile_eq_take_findIdx_not.symm

中文:
定理 list_takeWhile
  条件: {p : α -> 布尔值} (hp : Primrec p)
  结论: Primrec (列表.takeWhile p)
  证明: (list_take.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.takeWhile_eq_take_findIdx_not.symm

Depends on / 依赖: List.takeWhile_eq_take_findIdx_not.symm, Primrec, Primrec.id, Primrec.not.comp, hp.comp, list_findIdx, list_take, list_take.comp, of_eq, takeWhile_eq_take_findIdx_not
-/
theorem list_takeWhile {p : α -> Bool} (hp : Primrec p) : Primrec (List.takeWhile p) :=
  (list_take.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.takeWhile_eq_take_findIdx_not.symm

/--
theorem `list_dropWhile` / 定理 `list_dropWhile`

English:
theorem list_dropWhile
  given: {p : α -> Bool} (hp : Primrec p)
  statement: Primrec (List.dropWhile p)
  proof: (list_drop.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.dropWhile_eq_drop_findIdx_not.symm

中文:
定理 list_dropWhile
  条件: {p : α -> 布尔值} (hp : Primrec p)
  结论: Primrec (列表.dropWhile p)
  证明: (list_drop.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.dropWhile_eq_drop_findIdx_not.symm

Depends on / 依赖: List.dropWhile_eq_drop_findIdx_not.symm, Primrec, Primrec.id, Primrec.not.comp, dropWhile_eq_drop_findIdx_not, hp.comp, list_drop, list_drop.comp, list_findIdx, of_eq
-/
theorem list_dropWhile {p : α -> Bool} (hp : Primrec p) : Primrec (List.dropWhile p) :=
  (list_drop.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.dropWhile_eq_drop_findIdx_not.symm

/--
theorem `list_modifyHead'` / 定理 `list_modifyHead'`

English:
theorem list_modifyHead'
  given: {g : β -> α -> α} (hg : Primrec₂ g)
  proof: (list_casesOn fst (const [])
    (list_cons.comp (hg.comp (snd.comp fst) (fst.comp snd)) (snd.comp snd)).to₂).to₂.of_eq
    fun l b => by cases l <;> rfl

中文:
定理 list_modifyHead'
  条件: {g : β -> α -> α} (hg : Primrec₂ g)
  证明: (list_casesOn fst (const [])
    (list_cons.comp (hg.comp (snd.comp fst) (fst.comp snd)) (snd.comp snd)).to₂).to₂.of_eq
    fun l b => by cases l <;> rfl

Depends on / 依赖: fst.comp, hg.comp, list_casesOn, list_cons, list_cons.comp, of_eq, snd.comp
-/
theorem list_modifyHead' {g : β -> α -> α} (hg : Primrec₂ g) :
    Primrec₂ fun (l : List α) (b : β) => l.modifyHead (g b) :=
  (list_casesOn fst (const [])
    (list_cons.comp (hg.comp (snd.comp fst) (fst.comp snd)) (snd.comp snd)).to₂).to₂.of_eq
    fun l b => by cases l <;> rfl

/--
theorem `list_modifyHead` / 定理 `list_modifyHead`

English:
theorem list_modifyHead
  given: {f : α -> α} (hf : Primrec f)
  statement: Primrec (List.modifyHead f)
  proof: (list_modifyHead' (hf.comp snd).to₂).comp Primrec.id (const ())

中文:
定理 list_modifyHead
  条件: {f : α -> α} (hf : Primrec f)
  结论: Primrec (列表.modifyHead f)
  证明: (list_modifyHead' (hf.comp snd).to₂).comp Primrec.id (const ())

Depends on / 依赖: Primrec, Primrec.id, hf.comp, list_modifyHead
-/
theorem list_modifyHead {f : α -> α} (hf : Primrec f) : Primrec (List.modifyHead f) :=
  (list_modifyHead' (hf.comp snd).to₂).comp Primrec.id (const ())

/--
theorem `list_modify'` / 定理 `list_modify'`

English:
theorem list_modify'
  given: {g : β -> α -> α} (hg : Primrec₂ g)
  proof: -- l.modify n (g b) = l.take n ++ (l.drop n).modifyHead (g b)
  (list_append.comp
    (list_take.comp (fst.comp snd) fst)
    ((list_modifyHead' hg).comp (list_drop.comp (fst.comp snd) fst) (snd.comp snd))).to₂.of_eq
  fun l ⟨n, b⟩ => (List.modify_eq_take_drop (g b) l n).symm

中文:
定理 list_modify'
  条件: {g : β -> α -> α} (hg : Primrec₂ g)
  证明: -- l.modify n (g b) = l.take n ++ (l.drop n).modifyHead (g b)
  (list_append.comp
    (list_take.comp (fst.comp snd) fst)
    ((list_modifyHead' hg).comp (list_drop.comp (fst.comp snd) fst) (snd.comp snd))).to₂.of_eq
  fun l ⟨n, b⟩ => (List.modify_eq_take_drop (g b) l n).symm
-/
theorem list_modify' {g : β -> α -> α} (hg : Primrec₂ g) :
    Primrec₂ fun (l : List α) (p : Nat × β) => l.modify p.1 (g p.2) :=
  -- l.modify n (g b) = l.take n ++ (l.drop n).modifyHead (g b)
  (list_append.comp
    (list_take.comp (fst.comp snd) fst)
    ((list_modifyHead' hg).comp (list_drop.comp (fst.comp snd) fst) (snd.comp snd))).to₂.of_eq
  fun l ⟨n, b⟩ => (List.modify_eq_take_drop (g b) l n).symm

/--
theorem `list_modify` / 定理 `list_modify`

English:
theorem list_modify
  given: {f : α -> α} (hf : Primrec f)
  proof: ((list_modify' (hf.comp snd).to₂).comp fst (pair snd (const ()))).to₂

中文:
定理 list_modify
  条件: {f : α -> α} (hf : Primrec f)
  证明: ((list_modify' (hf.comp snd).to₂).comp fst (pair snd (const ()))).to₂

Depends on / 依赖: hf.comp, list_modify
-/
theorem list_modify {f : α -> α} (hf : Primrec f) :
    Primrec₂ fun (l : List α) (n : Nat) => l.modify n f :=
  ((list_modify' (hf.comp snd).to₂).comp fst (pair snd (const ()))).to₂

/--
theorem `list_set` / 定理 `list_set`

English:
theorem list_set
  statement: Primrec₂ fun (l : List α) (p : Nat × α) => l.set p.1 p.2
  proof: (list_modify' fst.to₂).of_eq fun l ⟨n, v⟩ => (List.set_eq_modify v n l).symm

中文:
定理 list_set
  结论: Primrec₂ fun (l : 列表 α) (p : 自然数 × α) => l.set p.1 p.2
  证明: (list_modify' fst.to₂).of_eq fun l ⟨n, v⟩ => (List.set_eq_modify v n l).symm

Depends on / 依赖: List.set_eq_modify, fst.to, list_modify, of_eq, set_eq_modify
-/
theorem list_set : Primrec₂ fun (l : List α) (p : Nat × α) => l.set p.1 p.2 :=
  (list_modify' fst.to₂).of_eq fun l ⟨n, v⟩ => (List.set_eq_modify v n l).symm

end Primrec

namespace PrimrecPred

open List Primrec

variable {α β : Type*} {p : α -> Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/--
theorem `exists_mem_list` / 定理 `exists_mem_list`

English:
theorem exists_mem_list
  statement: (hf : PrimrecPred p) -> PrimrecPred fun L : List α => exists a in L, p a

中文:
定理 存在_mem_list
  结论: (hf : PrimrecPred p) -> PrimrecPred fun L : 列表 α => 存在 a in L, p a
-/
theorem exists_mem_list : (hf : PrimrecPred p) -> PrimrecPred fun L : List α => exists a in L, p a
  | ⟨_, hf⟩ => .of_eq
(.not <| Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (const 0)) by simp

/--
theorem `forall_mem_list` / 定理 `forall_mem_list`

English:
theorem forall_mem_list
  statement: (hf : PrimrecPred p) -> PrimrecPred fun L : List α => forall a in L, p a

中文:
定理 对任意_mem_list
  结论: (hf : PrimrecPred p) -> PrimrecPred fun L : 列表 α => 对任意 a in L, p a
-/
theorem forall_mem_list : (hf : PrimrecPred p) -> PrimrecPred fun L : List α => forall a in L, p a
  | ⟨_, hf⟩ => .of_eq
(Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (list_length)) by simp

variable {p : Nat -> Prop}

/--
theorem `exists_lt` / 定理 `exists_lt`

English:
theorem exists_lt
  given: (hf : PrimrecPred p)
  statement: PrimrecPred fun n => exists x < n, p x
  proof: of_eq (hf.exists_mem_list.comp list_range) (by simp)

中文:
定理 存在_lt
  条件: (hf : PrimrecPred p)
  结论: PrimrecPred fun n => 存在 x < n, p x
  证明: of_eq (hf.exists_mem_list.comp list_range) (by simp)

Depends on / 依赖: exists_mem_list, hf.exists_mem_list.comp, list_range, of_eq
-/
theorem exists_lt (hf : PrimrecPred p) : PrimrecPred fun n => exists x < n, p x :=
  of_eq (hf.exists_mem_list.comp list_range) (by simp)

/--
theorem `forall_lt` / 定理 `forall_lt`

English:
theorem forall_lt
  given: (hf : PrimrecPred p)
  statement: PrimrecPred fun n => forall x < n, p x
  proof: of_eq (hf.forall_mem_list.comp list_range) (by simp)

中文:
定理 对任意_lt
  条件: (hf : PrimrecPred p)
  结论: PrimrecPred fun n => 对任意 x < n, p x
  证明: of_eq (hf.forall_mem_list.comp list_range) (by simp)

Depends on / 依赖: forall_mem_list, hf.forall_mem_list.comp, list_range, of_eq
-/
theorem forall_lt (hf : PrimrecPred p) : PrimrecPred fun n => forall x < n, p x :=
  of_eq (hf.forall_mem_list.comp list_range) (by simp)

/--
theorem `listFilter_listRange` / 定理 `listFilter_listRange`

English:
theorem listFilter_listRange
  given: {R : Nat -> Nat -> Prop} (s : Nat) [DecidableRel R] (hf : PrimrecRel R)
  proof: by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

中文:
定理 listFilter_listRange
  条件: {R : 自然数 -> 自然数 -> 命题} (s : 自然数) [DecidableRel R] (hf : PrimrecRel R)
  证明: by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

Depends on / 依赖: Option.none, Primrec, Primrec.eq.comp, filterMap_eq_filter, hf.decide.comp, listFilterMap, option_some_iff, option_some_iff.mpr
-/
theorem listFilter_listRange {R : Nat -> Nat -> Prop} (s : Nat) [DecidableRel R] (hf : PrimrecRel R) :
    Primrec fun n => (range s).filter (fun y => R y n) := by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

end PrimrecPred

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α -> β -> Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/--
theorem `listFilter` / 定理 `listFilter`

English:
theorem listFilter
  given: (hf : PrimrecRel R) [DecidableRel R]
  proof: by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact option_some.comp snd

中文:
定理 listFilter
  条件: (hf : PrimrecRel R) [DecidableRel R]
  证明: by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact option_some.comp snd

Depends on / 依赖: List.filterMap_eq_filter, Option.none, Primrec, Primrec.const, Primrec.eq.comp, Primrec.ite, filterMap_eq_filter, hf.decide.comp, listFilterMap, option_some, option_some.comp, snd.comp
-/
theorem listFilter (hf : PrimrecRel R) [DecidableRel R] :
    Primrec₂ fun (L : List α) b => L.filter (fun a => R a b) := by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact option_some.comp snd

/--
theorem `exists_mem_list` / 定理 `exists_mem_list`

English:
theorem exists_mem_list
  given: (hf : PrimrecRel R)
  statement: PrimrecRel fun (L : List α) b => exists a in L, R a b
  proof: by
  classical
  have h (L) (b) : (List.filter (R · b) L).length != 0 ↔ exists a in L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

中文:
定理 存在_mem_list
  条件: (hf : PrimrecRel R)
  结论: PrimrecRel fun (L : 列表 α) b => 存在 a in L, R a b
  证明: by
  classical
  have h (L) (b) : (List.filter (R · b) L).length != 0 ↔ exists a in L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

Depends on / 依赖: List.filter, Primrec, Primrec.eq.comp, classical, filter, hf.listFilter, length, listFilter, list_length, list_length.comp, of_eq
-/
theorem exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b => exists a in L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length != 0 ↔ exists a in L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

/--
theorem `forall_mem_list` / 定理 `forall_mem_list`

English:
theorem forall_mem_list
  given: (hf : PrimrecRel R)
  statement: PrimrecRel fun (L : List α) b => forall a in L, R a b
  proof: by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ forall a in L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

中文:
定理 对任意_mem_list
  条件: (hf : PrimrecRel R)
  结论: PrimrecRel fun (L : 列表 α) b => 对任意 a in L, R a b
  证明: by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ forall a in L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

Depends on / 依赖: L.length, List.filter, Primrec, Primrec.eq.comp, PrimrecRel, PrimrecRel.listFilter, PrimrecRel.of_eq, classical, filter, length, listFilter, list_length, list_length.comp, of_eq
-/
theorem forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b => forall a in L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ forall a in L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

variable {R : Nat -> Nat -> Prop}

/--
theorem `exists_lt` / 定理 `exists_lt`

English:
theorem exists_lt
  given: (hf : PrimrecRel R)
  statement: PrimrecRel fun n y => exists x < n, R x y
  proof: (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

中文:
定理 存在_lt
  条件: (hf : PrimrecRel R)
  结论: PrimrecRel fun n y => 存在 x < n, R x y
  证明: (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

Depends on / 依赖: exists_mem_list, hf.exists_mem_list.comp, list_range, list_range.comp, of_eq
-/
theorem exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y => exists x < n, R x y :=
  (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

/--
theorem `forall_lt` / 定理 `forall_lt`

English:
theorem forall_lt
  given: (hf : PrimrecRel R)
  statement: PrimrecRel fun n y => forall x < n, R x y
  proof: (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

中文:
定理 对任意_lt
  条件: (hf : PrimrecRel R)
  结论: PrimrecRel fun n y => 对任意 x < n, R x y
  证明: (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

Depends on / 依赖: forall_mem_list, hf.forall_mem_list.comp, list_range, list_range.comp, of_eq
-/
theorem forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y => forall x < n, R x y :=
  (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/--
Instance `vector` / 实例 `vector`

English:
instance vector
  signature: {n}
  body: fast_instance% subtype ((@Primrec.eq Nat _).comp list_length (const _))

中文:
实例 vector
  签名: {n}
  定义体: fast_instance% subtype ((@Primrec.eq Nat _).comp list_length (const _))

Depends on / 依赖: Primrec, Primrec.eq, fast_instance, list_length, subtype
-/
instance vector {n} : Primcodable (List.Vector α n) :=
  fast_instance% subtype ((@Primrec.eq Nat _).comp list_length (const _))

/--
Instance `finArrow` / 实例 `finArrow`

English:
instance finArrow
  signature: {n}
  body: ofEquiv _ (Equiv.vectorEquivFin _ _).symm

中文:
实例 finArrow
  签名: {n}
  定义体: ofEquiv _ (Equiv.vectorEquivFin _ _).symm

Depends on / 依赖: Equiv.vectorEquivFin, ofEquiv, vectorEquivFin
-/
instance finArrow {n} : Primcodable (Fin n -> α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/--
theorem `vector_toList` / 定理 `vector_toList`

English:
theorem vector_toList
  given: {n}
  statement: Primrec (@List.Vector.toList α n)
  proof: subtype_val (hp := (@Primrec.eq Nat _).comp list_length (const _))

中文:
定理 vector_toList
  条件: {n}
  结论: Primrec (@列表.Vector.toList α n)
  证明: subtype_val (hp := (@Primrec.eq Nat _).comp list_length (const _))

Depends on / 依赖: Primrec, Primrec.eq, list_length, subtype_val
-/
theorem vector_toList {n} : Primrec (@List.Vector.toList α n) :=
  subtype_val (hp := (@Primrec.eq Nat _).comp list_length (const _))

/--
theorem `vector_toList_iff` / 定理 `vector_toList_iff`

English:
theorem vector_toList_iff
  given: {n} {f : α -> List.Vector β n}
  proof: subtype_val_iff (hp := (@Primrec.eq Nat _).comp list_length (const _))

中文:
定理 vector_toList_iff
  条件: {n} {f : α -> 列表.Vector β n}
  证明: subtype_val_iff (hp := (@Primrec.eq Nat _).comp list_length (const _))

Depends on / 依赖: Primrec, Primrec.eq, list_length, subtype_val_iff
-/
theorem vector_toList_iff {n} {f : α -> List.Vector β n} :
    (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff (hp := (@Primrec.eq Nat _).comp list_length (const _))

/--
theorem `vector_cons` / 定理 `vector_cons`

English:
theorem vector_cons
  given: {n}
  statement: Primrec₂ (@List.Vector.cons α n)
  proof: vector_toList_iff.1 by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

中文:
定理 vector_cons
  条件: {n}
  结论: Primrec₂ (@列表.Vector.cons α n)
  证明: vector_toList_iff.1 by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

Depends on / 依赖: list_cons, list_cons.comp, vector_toList_iff
-/
theorem vector_cons {n} : Primrec₂ (@List.Vector.cons α n) :=
vector_toList_iff.1 by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

/--
theorem `vector_length` / 定理 `vector_length`

English:
theorem vector_length
  given: {n}
  statement: Primrec (@List.Vector.length α n)
  proof: const _

中文:
定理 vector_length
  条件: {n}
  结论: Primrec (@列表.Vector.length α n)
  证明: const _
-/
theorem vector_length {n} : Primrec (@List.Vector.length α n) :=
  const _

/--
theorem `vector_head` / 定理 `vector_head`

English:
theorem vector_head
  given: {n}
  statement: Primrec (@List.Vector.head α n)
  proof: option_some_iff.1 (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

中文:
定理 vector_head
  条件: {n}
  结论: Primrec (@列表.Vector.head α n)
  证明: option_some_iff.1 (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

Depends on / 依赖: list_head, of_eq, option_some_iff, vector_toList
-/
theorem vector_head {n} : Primrec (@List.Vector.head α n) :=
option_some_iff.1 (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

/--
theorem `vector_tail` / 定理 `vector_tail`

English:
theorem vector_tail
  given: {n}
  statement: Primrec (@List.Vector.tail α n)
  proof: vector_toList_iff.1 (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

中文:
定理 vector_tail
  条件: {n}
  结论: Primrec (@列表.Vector.tail α n)
  证明: vector_toList_iff.1 (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

Depends on / 依赖: list_tail, list_tail.comp, of_eq, vector_toList, vector_toList_iff
-/
theorem vector_tail {n} : Primrec (@List.Vector.tail α n) :=
vector_toList_iff.1 (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

/--
theorem `vector_get` / 定理 `vector_get`

English:
theorem vector_get
  given: {n}
  statement: Primrec₂ (@List.Vector.get α n)
  proof: option_some_iff.1
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]

中文:
定理 vector_get
  条件: {n}
  结论: Primrec₂ (@列表.Vector.get α n)
  证明: option_some_iff.1
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]

Depends on / 依赖: Vector, Vector.get_eq_get_toList, fin_val, fin_val.comp, get_eq_get_toList, list_getElem, of_eq, option_some_iff, vector_toList, vector_toList.comp
-/
theorem vector_get {n} : Primrec₂ (@List.Vector.get α n) :=
option_some_iff.1
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]

/--
theorem `list_ofFn` / 定理 `list_ofFn`

English:
theorem list_ofFn

中文:
定理 list_ofFn
-/
theorem list_ofFn :
    forall {n} {f : Fin n -> α -> σ}, (forall i, Primrec (f i)) -> Primrec fun a => List.ofFn fun i => f i a
  | 0, _, _ => by simp only [List.ofFn_zero]; exact const []
  | n + 1, f, hf => by
    simpa using list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

/--
theorem `vector_ofFn` / 定理 `vector_ofFn`

English:
theorem vector_ofFn
  given: {n} {f : Fin n -> α -> σ} (hf : forall i, Primrec (f i))
  proof: vector_toList_iff.1 by simp [list_ofFn hf]

中文:
定理 vector_ofFn
  条件: {n} {f : 有限集 n -> α -> σ} (hf : 对任意 i, Primrec (f i))
  证明: vector_toList_iff.1 by simp [list_ofFn hf]

Depends on / 依赖: list_ofFn, vector_toList_iff
-/
theorem vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall i, Primrec (f i)) :
    Primrec fun a => List.Vector.ofFn fun i => f i a :=
vector_toList_iff.1 by simp [list_ofFn hf]

/--
theorem `vector_get'` / 定理 `vector_get'`

English:
theorem vector_get'
  given: {n}
  statement: Primrec (@List.Vector.get α n)
  proof: of_equiv_symm

中文:
定理 vector_get'
  条件: {n}
  结论: Primrec (@列表.Vector.get α n)
  证明: of_equiv_symm

Depends on / 依赖: of_equiv_symm
-/
theorem vector_get' {n} : Primrec (@List.Vector.get α n) :=
  of_equiv_symm

/--
theorem `vector_ofFn'` / 定理 `vector_ofFn'`

English:
theorem vector_ofFn'
  given: {n}
  statement: Primrec (@List.Vector.ofFn α n)
  proof: of_equiv

中文:
定理 vector_ofFn'
  条件: {n}
  结论: Primrec (@列表.Vector.ofFn α n)
  证明: of_equiv

Depends on / 依赖: of_equiv
-/
theorem vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n) :=
  of_equiv

/--
theorem `fin_app` / 定理 `fin_app`

English:
theorem fin_app
  given: {n}
  statement: Primrec₂ (@id (Fin n -> σ))
  proof: (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

中文:
定理 fin_app
  条件: {n}
  结论: Primrec₂ (@id (有限集 n -> σ))
  证明: (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

Depends on / 依赖: of_eq, vector_get, vector_get.comp, vector_ofFn
-/
theorem fin_app {n} : Primrec₂ (@id (Fin n -> σ)) :=
  (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

/--
theorem `fin_curry₁` / 定理 `fin_curry₁`

English:
theorem fin_curry₁
  given: {n} {f : Fin n -> α -> σ}
  statement: Primrec₂ f ↔ forall i, Primrec (f i)
  proof: ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

中文:
定理 fin_curry₁
  条件: {n} {f : 有限集 n -> α -> σ}
  结论: Primrec₂ f ↔ 对任意 i, Primrec (f i)
  证明: ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

Depends on / 依赖: h.comp, of_eq, vector_get, vector_get.comp, vector_ofFn
-/
theorem fin_curry₁ {n} {f : Fin n -> α -> σ} : Primrec₂ f ↔ forall i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

/--
theorem `fin_curry` / 定理 `fin_curry`

English:
theorem fin_curry
  given: {n} {f : α -> Fin n -> σ}
  statement: Primrec f ↔ Primrec₂ f
  proof: ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

中文:
定理 fin_curry
  条件: {n} {f : α -> 有限集 n -> σ}
  结论: Primrec f ↔ Primrec₂ f
  证明: ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

Depends on / 依赖: Primrec, fin_app, fin_app.comp, h.comp, of_eq, vector_get, vector_ofFn
-/
theorem fin_curry {n} {f : α -> Fin n -> σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

end Primrec

namespace Nat

open List.Vector

/--
Inductive type `Primrec'` / 归纳类型 `Primrec'`

English:
inductive Primrec'
  parameters: : forall {n}, (List.Vector Nat n -> Nat) -> Prop
  constructors (5):
    - zero: @Primrec' 0 fun _ => 0
    - succ: @Primrec' 1 fun v => succ v.head
    - get: {n} (i : Fin n) : Primrec' fun v => v.get i
    - comp: {m n f} (g : Fin n -> List.Vector Nat m -> Nat) : Primrec' f -> (forall i, Primrec' (g i)) -> Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
    - prec: {n f g} : @Primrec' n f -> @Primrec' (n + 2) g -> Primrec' fun v : List.Vector Nat (n + 1) => v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

中文:
归纳类型 Primrec'
  参数: : 对任意 {n}, (列表.Vector 自然数 n -> 自然数) -> 命题
  构造子 (5 个):
    - zero: @Primrec' 0 fun _ => 0
    - succ: @Primrec' 1 fun v => succ v.head
    - get: {n} (i : 有限集 n) : Primrec' fun v => v.get i
    - comp: {m n f} (g : 有限集 n -> 列表.Vector 自然数 m -> 自然数) : Primrec' f -> (对任意 i, Primrec' (g i)) -> Primrec' fun a => f (列表.Vector.ofFn fun i => g i a)
    - prec: {n f g} : @Primrec' n f -> @Primrec' (n + 2) g -> Primrec' fun v : 列表.Vector 自然数 (n + 1) => v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)
-/
inductive Primrec' : forall {n}, (List.Vector Nat n -> Nat) -> Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n -> List.Vector Nat m -> Nat) :
      Primrec' f -> (forall i, Primrec' (g i)) -> Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f ->
        @Primrec' (n + 2) g ->
          Primrec' fun v : List.Vector Nat (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

end Nat

namespace Nat.Primrec'

open List.Vector

/--
theorem `to_prim` / 定理 `to_prim`

English:
theorem to_prim
  given: {n f} (pf : @Nat.Primrec' n f)
  statement: Primrec f
  proof: by
  induction pf with
  | zero => exact .const 0
  | succ => exact _root_.Primrec.succ.comp .vector_head
  | get i => exact Primrec.vector_get.comp .id (.const i)
  | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  | @prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (

中文:
定理 to_prim
  条件: {n f} (pf : @自然数.Primrec' n f)
  结论: Primrec f
  证明: by
  induction pf with
  | zero => exact .const 0
  | succ => exact _root_.Primrec.succ.comp .vector_head
  | get i => exact Primrec.vector_get.comp .id (.const i)
  | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  | @prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (

Depends on / 依赖: Primrec, Primrec.fst.comp, Primrec.snd.comp, Primrec.vector_cons.comp, Primrec.vector_get.comp, Primrec.vector_tail, _root_, _root_.Primrec.succ.comp, hf.comp, hg.comp, nat_rec, vector_cons, vector_get, vector_head, vector_ofFn, vector_tail
-/
theorem to_prim {n f} (pf : @Nat.Primrec' n f) : Primrec f := by
  induction pf with
  | zero => exact .const 0
  | succ => exact _root_.Primrec.succ.comp .vector_head
  | get i => exact Primrec.vector_get.comp .id (.const i)
  | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  | @prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (hf.comp Primrec.vector_tail)
        (hg.comp <|
Primrec.vector_cons.comp (Primrec.fst.comp .snd)
Primrec.vector_cons.comp (Primrec.snd.comp .snd)
            (@Primrec.vector_tail _ _ (n + 1)).comp .fst).to₂

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {n} {f g : List.Vector Nat n -> Nat} (hf : Primrec' f) (H : forall i, f i = g i)
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {n} {f g : 列表.Vector 自然数 n -> 自然数} (hf : Primrec' f) (H : 对任意 i, f i = g i)
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {n} {f g : List.Vector Nat n -> Nat} (hf : Primrec' f) (H : forall i, f i = g i) :
    Primrec' g :=
  (funext H : f = g) ▸ hf

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: {n}
  statement: forall m, @Primrec' n fun _ => m

中文:
定理 const
  条件: {n}
  结论: 对任意 m, @Primrec' n fun _ => m
-/
theorem const {n} : forall m, @Primrec' n fun _ => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0
  | m + 1 => succ.comp _ fun _ => const m

/--
theorem `head` / 定理 `head`

English:
theorem head
  given: {n : Nat}
  statement: @Primrec' n.succ head
  proof: (get 0).of_eq fun v => by simp [get_zero]

中文:
定理 head
  条件: {n : 自然数}
  结论: @Primrec' n.succ head
  证明: (get 0).of_eq fun v => by simp [get_zero]

Depends on / 依赖: get_zero, of_eq
-/
theorem head {n : Nat} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [get_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tail` / 定理 `tail`

English:
theorem tail
  given: {n f} (hf : @Primrec' n f)
  statement: @Primrec' n.succ fun v => f v.tail
  proof: (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

中文:
定理 tail
  条件: {n f} (hf : @Primrec' n f)
  结论: @Primrec' n.succ fun v => f v.tail
  证明: (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

Depends on / 依赖: hf.comp, i.succ, ofFn_get, of_eq, v.tail
-/
theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

/--
Definition of `Vec` / `Vec` 的定义

English:
definition Vec
  signature: {n m} (f : List.Vector Nat n -> List.Vector Nat m)
  body: forall i, Primrec' fun v => (f v).get i

中文:
定义 Vec
  签名: {n m} (f : 列表.Vector 自然数 n -> 列表.Vector 自然数 m)
  定义体: forall i, Primrec' fun v => (f v).get i

Depends on / 依赖: Primrec
-/
def Vec {n m} (f : List.Vector Nat n -> List.Vector Nat m) : Prop :=
  forall i, Primrec' fun v => (f v).get i

/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  given: {n}
  statement: @Vec n 0 fun _ => nil
  proof: fun i => i.elim0

中文:
定理 nil
  条件: {n}
  结论: @Vec n 0 fun _ => nil
  证明: fun i => i.elim0
-/
protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  given: {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g)
  proof: fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

中文:
定理 cons
  条件: {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g)
  证明: fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i
-/
protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

/--
theorem `idv` / 定理 `idv`

English:
theorem idv
  given: {n}
  statement: @Vec n n id
  proof: get

中文:
定理 idv
  条件: {n}
  结论: @Vec n n id
  证明: get
-/
theorem idv {n} : @Vec n n id :=
  get

/--
theorem `comp'` / 定理 `comp'`

English:
theorem comp'
  given: {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g)
  statement: Primrec' fun v => f (g v)
  proof: (hf.comp _ hg).of_eq fun v => by simp

中文:
定理 comp'
  条件: {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g)
  结论: Primrec' fun v => f (g v)
  证明: (hf.comp _ hg).of_eq fun v => by simp

Depends on / 依赖: hf.comp, of_eq
-/
theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

/--
theorem `comp₁` / 定理 `comp₁`

English:
theorem comp₁
  given: (f : Nat -> Nat) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g)
  proof: hf.comp _ fun _ => hg

中文:
定理 comp₁
  条件: (f : 自然数 -> 自然数) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g)
  证明: hf.comp _ fun _ => hg

Depends on / 依赖: hf.comp
-/
theorem comp₁ (f : Nat -> Nat) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun _ => hg

/--
theorem `comp₂` / 定理 `comp₂`

English:
theorem comp₂
  statement: (f : Nat -> Nat -> Nat) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
  proof: by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)

中文:
定理 comp₂
  结论: (f : 自然数 -> 自然数 -> 自然数) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
  证明: by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)

Depends on / 依赖: Primrec, hf.comp, hg.cons, hh.cons
-/
theorem comp₂ (f : Nat -> Nat -> Nat) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)

/--
theorem `prec'` / 定理 `prec'`

English:
theorem prec'
  given: {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h)
  proof: by
  simpa using comp' (prec hg hh) (hf.cons idv)

中文:
定理 prec'
  条件: {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h)
  证明: by
  simpa using comp' (prec hg hh) (hf.cons idv)

Depends on / 依赖: hf.cons
-/
theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : Nat => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)

/--
theorem `pred` / 定理 `pred`

English:
theorem pred
  statement: @Primrec' 1 fun v => v.head.pred
  proof: (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

中文:
定理 pred
  结论: @Primrec' 1 fun v => v.head.pred
  证明: (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

Depends on / 依赖: of_eq, v.head
-/
theorem pred : @Primrec' 1 fun v => v.head.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: @Primrec' 2 fun v => v.head + v.tail.head
  proof: (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]

中文:
定理 add
  结论: @Primrec' 2 fun v => v.head + v.tail.head
  证明: (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]

Depends on / 依赖: Nat.succ_add, of_eq, succ.comp, succ_add, v.head
-/
theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: @Primrec' 2 fun v => v.head - v.tail.head
  proof: by
  have : @Primrec' 2 fun v => (fun a b => b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

中文:
定理 sub
  结论: @Primrec' 2 fun v => v.head - v.tail.head
  证明: by
  have : @Primrec' 2 fun v => (fun a b => b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

Depends on / 依赖: Nat.sub_add_eq, Primrec, of_eq, pred.comp, sub_add_eq, v.head, v.tail.head
-/
theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
  have : @Primrec' 2 fun v => (fun a b => b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: @Primrec' 2 fun v => v.head * v.tail.head
  proof: (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

中文:
定理 mul
  结论: @Primrec' 2 fun v => v.head * v.tail.head
  证明: (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

Depends on / 依赖: Nat.succ_mul, add.comp, add_comm, of_eq, succ_mul, v.head
-/
theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

/--
theorem `if_lt` / 定理 `if_lt`

English:
theorem if_lt
  statement: {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
  proof: (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]

中文:
定理 if_lt
  结论: {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
  证明: (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]

Depends on / 依赖: Nat.lt_of_sub_eq_succ, Nat.sub_eq_zero_iff_le.mp, lt_of_sub_eq_succ, not_lt, of_eq, sub.comp, sub_eq_zero_iff_le
-/
theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]

/--
theorem `natPair` / 定理 `natPair`

English:
theorem natPair
  statement: @Primrec' 2 fun v => v.head.pair v.tail.head
  proof: if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

中文:
定理 natPair
  结论: @Primrec' 2 fun v => v.head.pair v.tail.head
  证明: if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

Depends on / 依赖: add.comp, if_lt, mul.comp
-/
theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

/--
theorem `encode` / 定理 `encode`

English:
theorem encode
  statement: forall {n}, @Primrec' n encode

中文:
定理 encode
  结论: 对任意 {n}, @Primrec' n encode
-/
protected theorem encode : forall {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
  | _ + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl

/--
theorem `sqrt` / 定理 `sqrt`

English:
theorem sqrt
  statement: @Primrec' 1 fun v => v.head.sqrt
  proof: by
  suffices H : forall n : Nat, n.sqrt =
      n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
    simp only [H, succ_eq_add_one]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head
          exact if x.succ < y.succ * y.succ t

中文:
定理 sqrt
  结论: @Primrec' 1 fun v => v.head.sqrt
  证明: by
  suffices H : forall n : Nat, n.sqrt =
      n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
    simp only [H, succ_eq_add_one]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head
          exact if x.succ < y.succ * y.succ t

Depends on / 依赖: Primrec, if_lt, introv, mul.comp, n.rec, n.sqrt, succ.comp, succ_eq_add_one, v.head, v.head.succ, v.tail.head, v.tail.head.succ, x.succ, y.succ
-/
theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
  suffices H : forall n : Nat, n.sqrt =
      n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
    simp only [H, succ_eq_add_one]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head
          exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) ?_
    · exact this
    have x1 : @Primrec' 3 fun v => v.head.succ := succ.comp₁ _ head
    have y1 : @Primrec' 3 fun v => v.tail.head.succ := succ.comp₁ _ (tail head)
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
  introv; symm
  induction n with
  | zero => simp
  | succ n IH =>
    dsimp; rw [IH]; split_ifs with h
    · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
    · exact Nat.eq_sqrt.2
⟨not_lt.1 h, Nat.sqrt_lt.1 Nat.lt_succ_iff.2 Nat.sqrt_succ_le_succ_sqrt _⟩

/--
theorem `unpair₁` / 定理 `unpair₁`

English:
theorem unpair₁
  given: {n f} (hf : @Primrec' n f)
  statement: @Primrec' n fun v => (f v).unpair.1
  proof: by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

中文:
定理 unpair₁
  条件: {n f} (hf : @Primrec' n f)
  结论: @Primrec' n fun v => (f v).unpair.1
  证明: by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

Depends on / 依赖: Nat.unpair, if_lt, mul.comp, of_eq, split_ifs, sqrt.comp, sub.comp, unpair
-/
theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

/--
theorem `unpair₂` / 定理 `unpair₂`

English:
theorem unpair₂
  given: {n f} (hf : @Primrec' n f)
  statement: @Primrec' n fun v => (f v).unpair.2
  proof: by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

中文:
定理 unpair₂
  条件: {n f} (hf : @Primrec' n f)
  结论: @Primrec' n fun v => (f v).unpair.2
  证明: by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

Depends on / 依赖: Nat.unpair, if_lt, mul.comp, of_eq, split_ifs, sqrt.comp, sub.comp, unpair
-/
theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

/--
theorem `of_prim` / 定理 `of_prim`

English:
theorem of_prim
  given: {n f}
  statement: Primrec f -> @Primrec' n f
  proof: suffices forall f, Nat.Primrec f -> @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector Nat n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf

中文:
定理 of_prim
  条件: {n f}
  结论: Primrec f -> @Primrec' n f
  证明: suffices forall f, Nat.Primrec f -> @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector Nat n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf

Depends on / 依赖: Encodable, Encodable.encode, List.Vector, Nat.Primrec, Primrec, Vector, decode, encode, encodek, hf.comp, natPair, natPair.comp, of_eq, pred.comp, v.head
-/
theorem of_prim {n f} : Primrec f -> @Primrec' n f :=
  suffices forall f, Nat.Primrec f -> @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector Nat n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf with
  | zero => exact const 0
  | succ => exact succ
  | left => exact unpair₁ head
  | right => exact unpair₂ head
  | pair _ _ hf hg => exact natPair.comp₂ _ hf hg
  | comp _ _ hf hg => exact hf.comp₁ _ hg
  | prec _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          natPair.comp₂ _ (unpair₁ <| tail <| tail head) (natPair.comp₂ _ head (tail head)))

/--
theorem `prim_iff` / 定理 `prim_iff`

English:
theorem prim_iff
  given: {n f}
  statement: @Primrec' n f ↔ Primrec f
  proof: ⟨to_prim, of_prim⟩

中文:
定理 prim_iff
  条件: {n f}
  结论: @Primrec' n f ↔ Primrec f
  证明: ⟨to_prim, of_prim⟩

Depends on / 依赖: of_prim, to_prim
-/
theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩

/--
theorem `prim_iff₁` / 定理 `prim_iff₁`

English:
theorem prim_iff₁
  given: {f : Nat -> Nat}
  statement: (@Primrec' 1 fun v => f v.head) ↔ Primrec f
  proof: prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩

中文:
定理 prim_iff₁
  条件: {f : 自然数 -> 自然数}
  结论: (@Primrec' 1 fun v => f v.head) ↔ Primrec f
  证明: prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩

Depends on / 依赖: h.comp, of_eq, prim_iff, prim_iff.trans, vector_head, vector_ofFn
-/
theorem prim_iff₁ {f : Nat -> Nat} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩

/--
theorem `prim_iff₂` / 定理 `prim_iff₂`

English:
theorem prim_iff₂
  given: {f : Nat -> Nat -> Nat}
  statement: (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f
  proof: prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩

中文:
定理 prim_iff₂
  条件: {f : 自然数 -> 自然数 -> 自然数}
  结论: (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f
  证明: prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩

Depends on / 依赖: Primrec, Primrec.vector_cons.comp, Primrec.vector_head.comp, h.comp, of_eq, prim_iff, prim_iff.trans, vector_cons, vector_head, vector_tail
-/
theorem prim_iff₂ {f : Nat -> Nat -> Nat} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩

/--
theorem `vec_iff` / 定理 `vec_iff`

English:
theorem vec_iff
  given: {m n f}
  statement: @Vec m n f ↔ Primrec f
  proof: ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
of_prim Primrec.vector_get.comp h (.const i)⟩

中文:
定理 vec_iff
  条件: {m n f}
  结论: @Vec m n f ↔ Primrec f
  证明: ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
of_prim Primrec.vector_get.comp h (.const i)⟩

Depends on / 依赖: Primrec, Primrec.vector_get.comp, Primrec.vector_ofFn, of_prim, to_prim, vector_get, vector_ofFn
-/
theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
of_prim Primrec.vector_get.comp h (.const i)⟩

end Nat.Primrec'

/--
theorem `Primrec.nat_sqrt` / 定理 `Primrec.nat_sqrt`

English:
theorem Primrec.nat_sqrt
  statement: Primrec Nat.sqrt
  proof: Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt

中文:
定理 Primrec.nat_sqrt
  结论: Primrec 自然数.sqrt
  证明: Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt

Depends on / 依赖: Nat.Primrec, Primrec
-/
theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
