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
/-
**prim** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def prim : Primcodable (List β) := ⟨H⟩
/-
**list_casesOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <|
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

set_option backward.privateInPublic true in
/-
**list_foldl'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  let := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
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
/-
**list_cons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem list_cons' : (haveI := prim H; Primrec₂ (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

set_option backward.privateInPublic true in
/-
**list_reverse'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
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
/-
**Primcodable.list** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：list : Primcodable (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List ℕ)
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List ℕ) n).reverse.foldl
          (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| .swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        rcases @decode α _ n.unpair.1 with - | a; · rfl
        simp only [Option.bind_some, Option.map_some]
        suffices ∀ (o : Option (List ℕ)) (p), encode o = encode p →
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

/-
**Primrec.list_cons** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_cons : Primrec₂ (@List.cons α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Primrec.List.0.list_cons'`：∀ {β : Type u_
2} [inst : Primcodable β] (H : Nat.Primrec fun n => Encodable.encode (Encodable.
decode n)),   Primrec₂ List.cons
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)
/-
**Primrec.list_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_casesOn {f : α -> List β} {g : α -> σ} {h : α -> β × List β -> σ} : P
rimrec f -> Primrec g -> Primrec₂ h -> @Primrec _ σ _ _ fun a => List.casesOn (f
 a) (g a) fun b l => h a (b, l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Primrec.List.0.list_casesOn'`：∀ {α : Type
 u_1} {β : Type u_2} {σ : Type u_3} [inst : Primcodable α] [inst_1 : Primcodable
 β] [inst_2 : Primcodable σ]   (H : Nat.Primrec f…
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' (Primcodable.prim _)
/-
**Primrec.list_foldl** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_foldl {f : α -> List β} {g : α -> σ} {h : α -> σ × β -> σ} : Primrec 
f -> Primrec g -> Primrec₂ h -> Primrec fun a => (f a).foldl (fun s b => h a (s,
 b)) (g a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Primrec.List.0.list_foldl'`：∀ {α : Type u
_1} {β : Type u_2} {σ : Type u_3} [inst : Primcodable α] [inst_1 : Primcodable β
] [inst_2 : Primcodable σ]   (H : Nat.Primrec f…
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)
/-
**Primrec.list_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_reverse : Primrec (@List.reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Primrec.List.0.list_reverse'`：∀ {β : Type
 u_2} [inst : Primcodable β] (H : Nat.Primrec fun n => Encodable.encode (Encodab
le.decode n)),   Primrec List.reverse
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)
/-
**Primrec.list_foldr** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> β × σ -> σ} (hf : Prim
rec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f a).foldr (fun b 
s => h a (b, s)) (g a)
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldl`：list_foldl {f : α -> List β} {g : α -> σ} {h : α -> 
σ × β -> σ} : Primrec f -> Primrec g -> Primrec₂ h -> Primrec fun a => (f a).fol
dl (fun …
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_reverse`：list_reverse : Primrec (@List.reverse α)
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : β 
→ α → β} {b : β},   List.foldl f b l.reverse = List.foldr (fun x y => f y x) b l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]
/-
**Primrec.list_head** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_head? : Primrec (@List.head? α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_head? : Primrec (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl
/-
**Primrec.list_headI** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_headI [Inhabited α] : Primrec (@List.headI α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.option_getD_default`：option_getD_default [Inhabited α] : Primrec
 (fun o : Option α => o.getD default)
· 使用定理 `Primrec.list_head?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Lis
t.head?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head!_eq_head?_getD`：∀ {α : Type u} [inst : Inhabited α] (l : List 
α), l.head! = l.head?.getD default
-/
theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_getD_default.comp list_head?).of_eq fun l => l.head!_eq_head?_getD.symm
/-
**Primrec.list_tail** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_tail : Primrec (@List.tail α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_casesOn`：list_casesOn {f : α -> List β} {g : α -> σ} {h : α
 -> β × List β -> σ} : Primrec f -> Primrec g -> Primrec₂ h -> @Primrec _ σ _ _ 
fun a => L…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem list_tail : Primrec (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl
/-
**Primrec.list_rec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_rec {f : α -> List β} {g : α -> σ} {h : α -> β × List β × σ -> σ} (hf
 : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Lis
t.recOn (f a) (g a) fun b l IH => h a (b, l, IH)
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction f a <;> simp [*]
/-
**Primrec.list_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_getElem? : Primrec₂ ((·[·]? : List α -> Nat -> Option α))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_getElem? : Primrec₂ ((·[·]? : List α → ℕ → Option α)) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : ℕ ⊕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => ℕ ⊕ α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (sumInr.comp <| snd.comp fst) (sumInl.comp snd).to₂).to₂
              (sumInr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
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
/-
**Primrec.list_getD** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_getD (d : α) : Primrec₂ fun l n => List.getD l n d
参数：d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec.option_getD`：option_getD : Primrec₂ (@Option.getD α)
· 使用定理 `Primrec.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec₂
 fun x1 x2 => x1[x2]?
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)
/-
**Primrec.list_getI** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_getI [Inhabited α] : Primrec₂ (@List.getI α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.list_getD`：list_getD (d : α) : Primrec₂ fun l n => List.getD l n
 d
-/
theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _
/-
**Primrec.list_append** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_append : Primrec₂ ((· ++ ·) : List α -> List α -> List α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]
/-
**Primrec.list_concat** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_concat : Primrec₂ fun l (a : α) => l ++ [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_append`：list_append : Primrec₂ ((· ++ ·) : List α -> List α
 -> List α)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))
/-
**Primrec.list_map** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_map {f : α -> List β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primre
c₂ g) : Primrec fun a => (f a).map (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]
/-
**Primrec.list_range** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_range : Primrec List.range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_rec'`：nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f
 a).re…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_concat`：list_concat : Primrec₂ fun l (a : α) => l ++ [a]
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
-/
theorem list_range : Primrec List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]
/-
**Primrec.list_flatten** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_flatten : Primrec (@List.flatten α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_append`：list_append : Primrec₂ ((· ++ ·) : List α -> List α
 -> List α)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem list_flatten : Primrec (@List.flatten α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]
/-
**Primrec.list_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_flatMap {f : α -> List β} {g : α -> β -> List σ} (hf : Primrec f) (hg
 : Primrec₂ g) : Primrec (fun a => (f a).flatMap (g a))
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_flatten`：list_flatten : Primrec (@List.flatten α)
· 使用定理 `Primrec.list_map`：list_map {f : α -> List β} {g : α -> β -> σ} (hf : Pri
mrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
-/
theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)
/-
**Primrec.optionToList** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：optionToList : Primrec (Option.toList : Option α -> List α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem optionToList : Primrec (Option.toList : Option α → List α) :=
  (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)
/-
**Primrec.listFilterMap** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：listFilterMap {f : α -> List β} {g : α -> β -> Option σ} (hf : Primrec f) 
(hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_flatMap`：list_flatMap {f : α -> List β} {g : α -> β -> List
 σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => (f a).flatMap (g a))
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.optionToList`：optionToList : Primrec (Option.toList : Option α -
> List α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.filterMap_eq_flatMap_toList`：filterMap_eq_flatMap_toList (f : α -> 
Option β) (l : List α) : l.filterMap f = l.flatMap fun a => (f a).toList
-/
theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
    fun _ ↦ Eq.symm <| List.filterMap_eq_flatMap_toList _ _

variable {p : α → Prop} [DecidablePred p]
/-
**Primrec.list_length** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_length : Primrec (@List.length α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
/-
**Primrec.listFilter** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：listFilter (hf : PrimrecPred p) : Primrec fun L => List.filter (p ·) L
参数：hf : PrimrecPred p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.filterMap_eq_filter`：∀ {α : Type u_1} {p : α → Bool}, List.filterMa
p (Option.guard fun x => p x) = List.filter p
· 使用定理 `Primrec.listFilterMap`：listFilterMap {f : α -> List β} {g : α -> β -> Op
tion σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g
 a)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecPred.comp`：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : 
PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred 
| ⟨_i,…
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x

--- 原说明 ---
Filtering a list for elements that satisfy a decidable predicate is primitive re
cursive.
-/
theorem listFilter (hf : PrimrecPred p) : Primrec fun L ↦ List.filter (p ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)
/-
**Primrec.list_findIdx** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_findIdx {f : α -> List β} {p : α -> β -> Bool} (hf : Primrec f) (hp :
 Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
参数：hf : Primrec f；hp : Primrec₂ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.findIdx_cons`：∀ {α : Type u_1} {p : α → Bool} {b : α} {l : List α},
 List.findIdx p (b :: l) = bif p b then 0 else List.findIdx p l + 1
-/
theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]
/-
**Primrec.list_idxOf** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_findIdx`：list_findIdx {f : α -> List β} {p : α -> β -> Bool
} (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec.beq`：∀ {α : Type u_1} [inst : Primcodable α] [inst_1 : Decidable
Eq α], Primrec₂ BEq.beq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
-/
theorem list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _) :=
  to₂ <| list_findIdx snd <| Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂
/-
**Primrec.nat_strong_rec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_strong_rec (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Pri
mrec₂ g) (H : forall a n, g a ((List.range n).map (f a)) = some (f a n)) : Primr
ec₂ f
参数：f : α -> Nat -> σ；hg : Primrec₂ g；H : forall a n, g a ((List.range n).map (f 
a)) = some (f a n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec₂.option_some_iff`：option_some_iff {f : α -> β -> σ} : (Primrec₂ 
fun a b => some (f a b)) ↔ Primrec₂ f
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.nat_rec`：nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Prim
rec f) (hg : Primrec₂ g) : Primrec₂ fun a (n : Nat) => n.rec (motive
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} (hf
 : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.list_concat`：list_concat : Primrec₂ fun l (a : α) => l ++ [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Primrec.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec₂
 fun x1 x2 => x1[x2]?
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 38 条，此处仅展示前 30 条）
-/
theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
  Primrec₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Primrec.listLookup** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：listLookup [DecidableEq α] : Primrec₂ (List.lookup : α -> List (α × β) -> 
Option β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_rec`：list_rec {f : α -> List β} {g : α -> σ} {h : α -> β × 
List β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : @Primrec 
_ σ _ …
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.beq`：∀ {α : Type u_1} [inst : Primcodable α] [inst_1 : Decidable
Eq α], Primrec₂ BEq.beq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem listLookup [DecidableEq α] : Primrec₂ (List.lookup : α → List (α × β) → Option β) :=
  (to₂ <| list_rec snd (const none) <|
    to₂ <|
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : a == p.1 <;> simp

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Primrec.nat_omega_rec'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_omega_rec' (f : β -> σ) {m : β -> Nat} {l : β -> List β} {g : β -> Lis
t σ -> Option σ} (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g) (Ord : fora
ll b, forall b' in l b, m b' < m b) (H : forall b, g b ((l b).map f) = some (f b
)) : Primrec f
参数：f : β -> σ；hm : Primrec m；hl : Primrec l；hg : Primrec₂ g；Ord : forall b, fora
ll b' in l b, m b' < m b；H : forall b, g b ((l b).map f) = some (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_flatMap`：list_flatMap {f : α -> List β} {g : α -> β -> List
 σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => (f a).flatMap (g a))
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.optionToList`：optionToList : Primrec (Option.toList : Option α -
> List α)
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec.listLookup`：listLookup [DecidableEq α] : Primrec₂ (List.lookup :
 α -> List (α × β) -> Option β)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec.nat_rec'`：nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f
 a).re…
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.listFilterMap`：listFilterMap {f : α -> List β} {g : α -> β -> Op
tion σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g
 a)
· 使用定理 `Primrec.nat_sub`：nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} (hf
 : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
· 使用定理 `Primrec₂.pair`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [i
nst_1 : Primcodable β], Primrec₂ Prod.mk
· 使用定理 `Primrec.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec₂
 fun x1 x2 => x1[x2]?
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 69 条，此处仅展示前 30 条）
-/
theorem nat_omega_rec' (f : β → σ) {m : β → ℕ} {l : β → List β} {g : β → List σ → Option σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
    (Ord : ∀ b, ∀ b' ∈ l b, m b' < m b)
    (H : ∀ b, g b ((l b).map f) = some (f b)) : Primrec f := by
  have : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : ℕ → List β := fun n ↦ n.rec [b] fun _ bs ↦ bs.flatMap l
  let graph (b : β) : ℕ → List (β × σ) := fun i ↦ i.rec [] fun i ih ↦
    (bindList b (m b - i)).filterMap fun b' ↦ (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : Primrec₂ mapGraph :=
    to₂ <| list_flatMap snd <| optionToList.comp₂ <| listLookup.comp₂ .right (fst.comp₂ .left)
  have bindList_primrec : Primrec₂ (bindList) :=
    nat_rec' snd
      (list_cons.comp fst (const []))
      (to₂ <| list_flatMap (snd.comp snd) (hl.comp₂ .right))
  have graph_primrec : Primrec₂ (graph) :=
    to₂ <| nat_rec' snd (const []) <|
      to₂ <| listFilterMap
        (bindList_primrec.comp
          (fst.comp fst)
          (nat_sub.comp (hm.comp <| fst.comp fst) (fst.comp snd))) <|
            to₂ <| option_map
              (hg.comp snd (mapGraph_primrec.comp (snd.comp <| snd.comp fst) (hl.comp snd)))
              (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right)
  have : Primrec (fun b => (graph b (m b + 1))[0]?.map Prod.snd) :=
    option_map (list_getElem?.comp (graph_primrec.comp Primrec.id (succ.comp hm)) (const 0))
      (snd.comp₂ Primrec₂.right)
  exact option_some_iff.mp <| this.of_eq <| fun b ↦ by
    have graph_eq_map_bindList (i : ℕ) (hi : i ≤ m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x ↦ (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : ℕ) : ∀ b' ∈ bindList b k, m b' < m b + 1 - k := by
          induction k with simp [bindList]
          | succ k ih =>
            grind
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' ⊆ bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction bs' with simp [mapGraph]
        | cons b bs' ih =>
          have : b ∈ bs ∧ bs' ⊆ bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : ∀ i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : ∀ i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
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
/-
**Primrec.nat_omega_rec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_omega_rec (f : α -> β -> σ) {m : α -> β -> Nat} {l : α -> β -> List β}
 {g : α -> β × List σ -> Option σ} (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Pri
mrec₂ g) (Ord : forall a b, forall b' in l a b, m a b' < m a b) (H : forall a b,
 g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f
参数：f : α -> β -> σ；hm : Primrec₂ m；hl : Primrec₂ l；hg : Primrec₂ g；Ord : forall 
a b, forall b' in l a b, m a b' < m a b；H : forall a b, g a (b, (l a b).map (f a
)) = some (f a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec₂.uncurry`：uncurry {f : α -> β -> σ} : Primrec (Function.uncurry 
f) ↔ Primrec₂ f
· 使用定理 `Primrec.nat_omega_rec'`：nat_omega_rec' (f : β -> σ) {m : β -> Nat} {l : 
β -> List β} {g : β -> List σ -> Option σ} (hm : Primrec m) (hl : Primrec l) (hg
 : Primrec₂ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.list_map`：list_map {f : α -> List β} {g : α -> β -> σ} (hf : Pri
mrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec₂.pair`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [i
nst_1 : Primcodable β], Primrec₂ Prod.mk
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem nat_omega_rec (f : α → β → σ) {m : α → β → ℕ}
    {l : α → β → List β} {g : α → β × List σ → Option σ}
    (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Primrec₂ g)
    (Ord : ∀ a b, ∀ b' ∈ l a b, m a b' < m a b)
    (H : ∀ a b, g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f :=
  Primrec₂.uncurry.mp <|
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using! Ord) (by simpa [Function.comp] using! H)

/-- `List.drop` is primitive recursive. -/
/-
**Primrec.list_drop** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_drop : Primrec₂ (List.drop : Nat -> List α -> List α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.nat_iterate`：nat_iterate {f : α -> Nat} {g : α -> β} {h : α -> β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (h
 a)^[f a]…
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.list_tail`：list_tail : Primrec (@List.tail α)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `List.tail_iterate`：tail_iterate (l : List α) (n : Nat) : (List.tail^[n])
 l = l.drop n

--- 原说明 ---
`List.drop` is primitive recursive.
-/
theorem list_drop : Primrec₂ (List.drop : ℕ → List α → List α) :=
  (nat_iterate fst snd (list_tail.comp₂ .right)).to₂.of_eq fun n l => l.tail_iterate n

/-- `List.take` is primitive recursive. -/
/-
**Primrec.list_take** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_take : Primrec₂ (List.take : Nat -> List α -> List α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_reverse`：list_reverse : Primrec (@List.reverse α)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_drop`：list_drop : Primrec₂ (List.drop : Nat -> List α -> Li
st α)
· 使用定理 `Primrec.nat_sub`：nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.reverse_take`：∀ {α : Type u_1} {l : List α} {i : ℕ}, (List.take i l
).reverse = List.drop (l.length - i) l.reverse

--- 原说明 ---
`List.take` is primitive recursive.
-/
theorem list_take : Primrec₂ (List.take : ℕ → List α → List α) :=
  (list_reverse.comp (list_drop.comp (nat_sub.comp (list_length.comp snd) fst)
    (list_reverse.comp snd))).of_eq fun ⟨n, l⟩ => by
    rw [← List.reverse_reverse (l.take n), List.reverse_take]

/-- `List.takeWhile` is primitive recursive. -/
/-
**Primrec.list_takeWhile** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_takeWhile {p : α -> Bool} (hp : Primrec p) : Primrec (List.takeWhile 
p)
参数：hp : Primrec p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_take`：list_take : Primrec₂ (List.take : Nat -> List α -> Li
st α)
· 使用定理 `Primrec.list_findIdx`：list_findIdx {f : α -> List β} {p : α -> β -> Bool
} (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.not`：Primrec not
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.takeWhile_eq_take_findIdx_not`：∀ {α : Type u_1} {xs : List α} {p : 
α → Bool}, List.takeWhile p xs = List.take (List.findIdx (fun a => !p a) xs) xs

--- 原说明 ---
`List.takeWhile` is primitive recursive.
-/
theorem list_takeWhile {p : α → Bool} (hp : Primrec p) : Primrec (List.takeWhile p) :=
  (list_take.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.takeWhile_eq_take_findIdx_not.symm

/-- `List.dropWhile` is primitive recursive. -/
/-
**Primrec.list_dropWhile** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_dropWhile {p : α -> Bool} (hp : Primrec p) : Primrec (List.dropWhile 
p)
参数：hp : Primrec p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_drop`：list_drop : Primrec₂ (List.drop : Nat -> List α -> Li
st α)
· 使用定理 `Primrec.list_findIdx`：list_findIdx {f : α -> List β} {p : α -> β -> Bool
} (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.not`：Primrec not
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dropWhile_eq_drop_findIdx_not`：∀ {α : Type u_1} {xs : List α} {p : 
α → Bool}, List.dropWhile p xs = List.drop (List.findIdx (fun a => !p a) xs) xs

--- 原说明 ---
`List.dropWhile` is primitive recursive.
-/
theorem list_dropWhile {p : α → Bool} (hp : Primrec p) : Primrec (List.dropWhile p) :=
  (list_drop.comp (list_findIdx Primrec.id (Primrec.not.comp (hp.comp snd)).to₂)
    Primrec.id).of_eq fun _ => List.dropWhile_eq_drop_findIdx_not.symm

/-- `List.modifyHead` with a function depending on external data is primitive recursive. -/
/-
**Primrec.list_modifyHead'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_modifyHead' {g : β -> α -> α} (hg : Primrec₂ g) : Primrec₂ fun (l : L
ist α) (b : β) => l.modifyHead (g b)
参数：hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_casesOn`：list_casesOn {f : α -> List β} {g : α -> σ} {h : α
 -> β × List β -> σ} : Primrec f -> Primrec g -> Primrec₂ h -> @Primrec _ σ _ _ 
fun a => L…
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`List.modifyHead` with a function depending on external data is primitive recurs
ive.
-/
theorem list_modifyHead' {g : β → α → α} (hg : Primrec₂ g) :
    Primrec₂ fun (l : List α) (b : β) => l.modifyHead (g b) :=
  (list_casesOn fst (const [])
    (list_cons.comp (hg.comp (snd.comp fst) (fst.comp snd)) (snd.comp snd)).to₂).to₂.of_eq
    fun l b => by cases l <;> rfl

/-- `List.modifyHead` by a primitive recursive function is primitive recursive. -/
/-
**Primrec.list_modifyHead** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_modifyHead {f : α -> α} (hf : Primrec f) : Primrec (List.modifyHead f
)
参数：hf : Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_modifyHead'`：list_modifyHead' {g : β -> α -> α} (hg : Primr
ec₂ g) : Primrec₂ fun (l : List α) (b : β) => l.modifyHead (g b)
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x

--- 原说明 ---
`List.modifyHead` by a primitive recursive function is primitive recursive.
-/
theorem list_modifyHead {f : α → α} (hf : Primrec f) : Primrec (List.modifyHead f) :=
  (list_modifyHead' (hf.comp snd).to₂).comp Primrec.id (const ())

/-- `List.modify` with a function depending on external data is primitive recursive. -/
/-
**Primrec.list_modify'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_modify' {g : β -> α -> α} (hg : Primrec₂ g) : Primrec₂ fun (l : List 
α) (p : Nat × β) => l.modify p.1 (g p.2)
参数：hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_append`：list_append : Primrec₂ ((· ++ ·) : List α -> List α
 -> List α)
· 使用定理 `Primrec.list_take`：list_take : Primrec₂ (List.take : Nat -> List α -> Li
st α)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.list_modifyHead'`：list_modifyHead' {g : β -> α -> α} (hg : Primr
ec₂ g) : Primrec₂ fun (l : List α) (b : β) => l.modifyHead (g b)
· 使用定理 `Primrec.list_drop`：list_drop : Primrec₂ (List.drop : Nat -> List α -> Li
st α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.modify_eq_take_drop`：∀ {α : Type u_1} (f : α → α) (l : List α) (i :
 ℕ), l.modify i f = List.take i l ++ List.modifyHead f (List.drop i l)

--- 原说明 ---
`List.modify` with a function depending on external data is primitive recursive.
-/
theorem list_modify' {g : β → α → α} (hg : Primrec₂ g) :
    Primrec₂ fun (l : List α) (p : ℕ × β) => l.modify p.1 (g p.2) :=
  -- l.modify n (g b) = l.take n ++ (l.drop n).modifyHead (g b)
  (list_append.comp
    (list_take.comp (fst.comp snd) fst)
    ((list_modifyHead' hg).comp (list_drop.comp (fst.comp snd) fst) (snd.comp snd))).to₂.of_eq
  fun l ⟨n, b⟩ => (List.modify_eq_take_drop (g b) l n).symm

/-- `List.modify` by a primitive recursive function is primitive recursive. -/
/-
**Primrec.list_modify** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_modify {f : α -> α} (hf : Primrec f) : Primrec₂ fun (l : List α) (n :
 Nat) => l.modify n f
参数：hf : Primrec f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_modify'`：list_modify' {g : β -> α -> α} (hg : Primrec₂ g) :
 Primrec₂ fun (l : List α) (p : Nat × β) => l.modify p.1 (g p.2)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x

--- 原说明 ---
`List.modify` by a primitive recursive function is primitive recursive.
-/
theorem list_modify {f : α → α} (hf : Primrec f) :
    Primrec₂ fun (l : List α) (n : ℕ) => l.modify n f :=
  ((list_modify' (hf.comp snd).to₂).comp fst (pair snd (const ()))).to₂

/-- `List.set` is primitive recursive. -/
/-
**Primrec.list_set** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_set : Primrec₂ fun (l : List α) (p : Nat × α) => l.set p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.list_modify'`：list_modify' {g : β -> α -> α} (hg : Primrec₂ g) :
 Primrec₂ fun (l : List α) (p : Nat × β) => l.modify p.1 (g p.2)
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.set_eq_modify`：∀ {α : Type u_1} (a : α) (n : ℕ) (l : List α), l.set
 n a = l.modify n fun x => a

--- 原说明 ---
`List.set` is primitive recursive.
-/
theorem list_set : Primrec₂ fun (l : List α) (p : ℕ × α) => l.set p.1 p.2 :=
  (list_modify' fst.to₂).of_eq fun l ⟨n, v⟩ => (List.set_eq_modify v n l).symm

end Primrec

namespace PrimrecPred

open List Primrec

variable {α β : Type*} {p : α → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
/-
**PrimrecPred.exists_mem_list** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : Primcodable α], PrimrecPred p → Pr
imrecPred fun L => ∃ a ∈ L, p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecPred.not`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop},
 PrimrecPred p → PrimrecPred fun a => ¬p a
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Primrec.listFilter`：listFilter (hf : PrimrecPred p) : Primrec fun L => L
ist.filter (p ·) L
· 使用引理 `Primrec.primrecPred`：Primrec.primrecPred {p : α -> Prop} [DecidablePred 
p] (hp : Primrec (fun a => decide (p a))) : PrimrecPred p
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Checking if any element of a list satisfies a decidable predicate is primitive r
ecursive.
-/
theorem exists_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∃ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (.not <| Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (const 0)) <| by simp

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
/-
**PrimrecPred.forall_mem_list** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : Primcodable α], PrimrecPred p → Pr
imrecPred fun L => ∀ a ∈ L, p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Primrec.listFilter`：listFilter (hf : PrimrecPred p) : Primrec fun L => L
ist.filter (p ·) L
· 使用引理 `Primrec.primrecPred`：Primrec.primrecPred {p : α -> Prop} [DecidablePred 
p] (hp : Primrec (fun a => decide (p a))) : PrimrecPred p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Checking if every element of a list satisfies a decidable predicate is primitive
 recursive.
-/
theorem forall_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∀ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (list_length)) <| by simp

variable {p : ℕ → Prop}

/-- Bounded existential quantifiers are primitive recursive. -/
/-
**PrimrecPred.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：exists_lt (hf : PrimrecPred p) : PrimrecPred fun n => exists x < n, p x
参数：hf : PrimrecPred p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecPred.comp`：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : 
PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred 
| ⟨_i,…
· 使用定理 `PrimrecPred.exists_mem_list`：∀ {α : Type u_1} {p : α → Prop} [inst : Pri
mcodable α], PrimrecPred p → PrimrecPred fun L => ∃ a ∈ L, p a
· 使用定理 `Primrec.list_range`：list_range : Primrec List.range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Bounded existential quantifiers are primitive recursive.
-/
theorem exists_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∃ x < n, p x :=
  of_eq (hf.exists_mem_list.comp list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
/-
**PrimrecPred.forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：forall_lt (hf : PrimrecPred p) : PrimrecPred fun n => forall x < n, p x
参数：hf : PrimrecPred p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecPred.comp`：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : 
PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred 
| ⟨_i,…
· 使用定理 `PrimrecPred.forall_mem_list`：∀ {α : Type u_1} {p : α → Prop} [inst : Pri
mcodable α], PrimrecPred p → PrimrecPred fun L => ∀ a ∈ L, p a
· 使用定理 `Primrec.list_range`：list_range : Primrec List.range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Bounded universal quantifiers are primitive recursive.
-/
theorem forall_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∀ x < n, p x :=
  of_eq (hf.forall_mem_list.comp list_range) (by simp)

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
/-
**PrimrecPred.listFilter_listRange** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：listFilter_listRange {R : Nat -> Nat -> Prop} (s : Nat) [DecidableRel R] (
hf : PrimrecRel R) : Primrec fun n => (range s).filter (fun y => R y n)
参数：s : Nat；hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Primrec.listFilterMap`：listFilterMap {f : α -> List β} {g : α -> β -> Op
tion σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g
 a)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `PrimrecRel.decide`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α
] [inst_1 : Primcodable β] {R : α → β → Prop}   [inst_2 : DecidableRel R], Primr
ecRel R…
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f

--- 原说明 ---
A helper lemma for proofs about bounded quantifiers on decidable relations.
-/
theorem listFilter_listRange {R : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel R] (hf : PrimrecRel R) :
    Primrec fun n ↦ (range s).filter (fun y ↦ R y n) := by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

end PrimrecPred

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, it is primitive recursive
to filter `L` for elements `a` with `R a b` -/
/-
**PrimrecRel.listFilter** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：listFilter (hf : PrimrecRel R) [DecidableRel R] : Primrec₂ fun (L : List α
) b => L.filter (fun a => R a b)
参数：hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Primrec.listFilterMap`：listFilterMap {f : α -> List β} {g : α -> β -> Op
tion σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g
 a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `PrimrecRel.decide`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α
] [inst_1 : Primcodable β] {R : α → β → Prop}   [inst_2 : DecidableRel R], Primr
ecRel R…
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)

--- 原说明 ---
If `R a b` is decidable, then given `L : List α` and `b : β`, it is primitive re
cursive
to filter `L` for elements `a` with `R a b`
-/
theorem listFilter (hf : PrimrecRel R) [DecidableRel R] :
    Primrec₂ fun (L : List α) b ↦ L.filter (fun a ↦ R a b) := by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact option_some.comp snd

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∃ a L, R a b`
is a primitive recursive relation. -/
/-
**PrimrecRel.exists_mem_list** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b => exi
sts a in L, R a b
参数：hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `PrimrecRel.of_eq`：PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β]
 {r s : α -> β -> Prop} (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : Pr
imrecR…
· 使用定理 `PrimrecRel.not`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} [inst
 : Primcodable α] [inst_1 : Primcodable β],   PrimrecRel R → PrimrecRel fun a b 
=> ¬…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `PrimrecRel.listFilter`：listFilter (hf : PrimrecRel R) [DecidableRel R] :
 Primrec₂ fun (L : List α) b => L.filter (fun a => R a b)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x

--- 原说明 ---
If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∃ a L, R 
a b`
is a primitive recursive relation.
-/
theorem exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∃ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length ≠ 0 ↔ ∃ a ∈ L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∀ a L, R a b`
is a primitive recursive relation. -/
/-
**PrimrecRel.forall_mem_list** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b => for
all a in L, R a b
参数：hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `PrimrecRel.of_eq`：PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β]
 {r s : α -> β -> Prop} (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : Pr
imrecR…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `PrimrecRel.listFilter`：listFilter (hf : PrimrecRel R) [DecidableRel R] :
 Primrec₂ fun (L : List α) b => L.filter (fun a => R a b)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)

--- 原说明 ---
If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∀ a L, R 
a b`
is a primitive recursive relation.
-/
theorem forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∀ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ ∀ a ∈ L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

variable {R : ℕ → ℕ → Prop}

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∃ x < n, R x y` is a
primitive recursive relation. -/
/-
**PrimrecRel.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y => exists x < n, R x y
参数：hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `PrimrecRel.exists_mem_list`：exists_mem_list (hf : PrimrecRel R) : Primre
cRel fun (L : List α) b => exists a in L, R a b
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_range`：list_range : Primrec List.range
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∃ x < n, R x y
` is a
primitive recursive relation.
-/
theorem exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∀ x < n, R x y` is a
primitive recursive relation. -/
/-
**PrimrecRel.forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y => forall x < n, R x y
参数：hf : PrimrecRel R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `PrimrecRel.forall_mem_list`：forall_mem_list (hf : PrimrecRel R) : Primre
cRel fun (L : List α) b => forall a in L, R a b
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_range`：list_range : Primrec List.range
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∀ x < n, R x y
` is a
primitive recursive relation.
-/
theorem forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/-
**Primcodable.vector** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：vector {n} : Primcodable (List.Vector α n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance vector {n} : Primcodable (List.Vector α n) :=
  fast_instance% subtype ((@Primrec.eq ℕ _).comp list_length (const _))
/-
**Primcodable.finArrow** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：finArrow {n} : Primcodable (Fin n -> α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/-
**Primrec.vector_toList** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_toList {n} : Primrec (@List.Vector.toList α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.subtype_val`：subtype_val {p : α -> Prop} [DecidablePred p] {hp :
 PrimrecPred p} : haveI
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem vector_toList {n} : Primrec (@List.Vector.toList α n) :=
  subtype_val (hp := (@Primrec.eq ℕ _).comp list_length (const _))
/-
**Primrec.vector_toList_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_toList_iff {n} {f : α -> List.Vector β n} : (Primrec fun a => (f a)
.toList) ↔ Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.subtype_val_iff`：subtype_val_iff {p : β -> Prop} [DecidablePred 
p] {hp : PrimrecPred p} {f : α -> Subtype p} : haveI
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem vector_toList_iff {n} {f : α → List.Vector β n} :
    (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff (hp := (@Primrec.eq ℕ _).comp list_length (const _))
/-
**Primrec.vector_cons** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_cons {n} : Primrec₂ (@List.Vector.cons α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.vector_toList_iff`：vector_toList_iff {n} {f : α -> List.Vector β
 n} : (Primrec fun a => (f a).toList) ↔ Primrec f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
theorem vector_cons {n} : Primrec₂ (@List.Vector.cons α n) :=
  vector_toList_iff.1 <| by simpa using list_cons.comp fst (vector_toList_iff.2 snd)
/-
**Primrec.vector_length** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_length {n} : Primrec (@List.Vector.length α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem vector_length {n} : Primrec (@List.Vector.length α n) :=
  const _
/-
**Primrec.vector_head** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_head {n} : Primrec (@List.Vector.head α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_head?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Lis
t.head?
· 使用定理 `Primrec.vector_toList`：vector_toList {n} : Primrec (@List.Vector.toList 
α n)
-/
theorem vector_head {n} : Primrec (@List.Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl
/-
**Primrec.vector_tail** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_tail {n} : Primrec (@List.Vector.tail α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.vector_toList_iff`：vector_toList_iff {n} {f : α -> List.Vector β
 n} : (Primrec fun a => (f a).toList) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_tail`：list_tail : Primrec (@List.tail α)
· 使用定理 `Primrec.vector_toList`：vector_toList {n} : Primrec (@List.Vector.toList 
α n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem vector_tail {n} : Primrec (@List.Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl
/-
**Primrec.vector_get** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_get {n} : Primrec₂ (@List.Vector.get α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Primrec₂
 fun x1 x2 => x1[x2]?
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.vector_toList`：vector_toList {n} : Primrec (@List.Vector.toList 
α n)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.fin_val`：fin_val {n} : Primrec (fun (i : Fin n) => (i : Nat))
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vector_get {n} : Primrec₂ (@List.Vector.get α n) :=
  option_some_iff.1 <|
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]
/-
**Primrec.list_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_3} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {n : ℕ} {f : Fin n → α → σ},   (∀ (i : Fin n), Primrec (f i)) → Primrec fu
n a => List.ofFn fun i => f i a
参数：∀ (i : Fin n), Primrec (f i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, _, _ => by simp only [List.ofFn_zero]; exact const []
  | n + 1, f, hf => by
    simpa using list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)
/-
**Primrec.vector_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall i, Primrec (f i)) : Pri
mrec fun a => List.Vector.ofFn fun i => f i a
参数：hf : forall i, Primrec (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.vector_toList_iff`：vector_toList_iff {n} {f : α -> List.Vector β
 n} : (Primrec fun a => (f a).toList) ↔ Primrec f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Vector.toList_ofFn`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), (List
.Vector.ofFn f).toList = List.ofFn f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Primrec.list_ofFn`：∀ {α : Type u_1} {σ : Type u_3} [inst : Primcodable α
] [inst_1 : Primcodable σ] {n : ℕ} {f : Fin n → α → σ},   (∀ (i : Fin n), Primre
c (f i)…
-/
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => List.Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_ofFn hf]
/-
**Primrec.vector_get'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_get' {n} : Primrec (@List.Vector.get α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_equiv_symm`：of_equiv_symm {β} {e : β ≃ α} : haveI
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem vector_get' {n} : Primrec (@List.Vector.get α n) :=
  of_equiv_symm
/-
**Primrec.vector_ofFn'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_equiv`：of_equiv {β} {e : β ≃ α} : haveI
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n) :=
  of_equiv
/-
**Primrec.fin_app** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_app {n} : Primrec₂ (@id (Fin n -> σ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.vector_get`：vector_get {n} : Primrec₂ (@List.Vector.get α n)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.vector_ofFn'`：vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp
/-
**Primrec.fin_curry** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_curry {n} {f : α -> Fin n -> σ} : Primrec f ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fin_app`：fin_app {n} : Primrec₂ (@id (Fin n -> σ))
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.vector_get'`：vector_get' {n} : Primrec (@List.Vector.get α n)
· 使用定理 `Primrec.vector_ofFn`：vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall 
i, Primrec (f i)) : Primrec fun a => List.Vector.ofFn fun i => f i a
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩
/-
**Primrec.fin_curry** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_curry {n} {f : α -> Fin n -> σ} : Primrec f ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fin_app`：fin_app {n} : Primrec₂ (@id (Fin n -> σ))
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.vector_get'`：vector_get' {n} : Primrec (@List.Vector.get α n)
· 使用定理 `Primrec.vector_ofFn`：vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall 
i, Primrec (f i)) : Primrec fun a => List.Vector.ofFn fun i => f i a
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

end Primrec

namespace Nat

open List.Vector

/-- An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
/-
**Nat.Primrec'** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：{n : ℕ} → (List.Vector ℕ n → ℕ) → Prop
参数：List.Vector ℕ n → ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`.
-/
inductive Primrec' : ∀ {n}, (List.Vector ℕ n → ℕ) → Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
      Primrec' f → (∀ i, Primrec' (g i)) → Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f →
        @Primrec' (n + 2) g →
          Primrec' fun v : List.Vector ℕ (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

end Nat

namespace Nat.Primrec'

open List.Vector

/-
**Nat.Primrec.to_prim** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
          Primrec.vector_cons.comp (Primrec.fst.comp .snd) <|
          Primrec.vector_cons.comp (Primrec.snd.comp .snd) <|
            (@Primrec.vector_tail _ _ (n + 1)).comp .fst).to₂
/-
**Nat.Primrec.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : forall n, f n = g n) : 
Nat.Primrec g
参数：hf : Nat.Primrec f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) :
    Primrec' g :=
  (funext H : f = g) ▸ hf
/-
**Nat.Primrec.const** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：const : forall n : Nat, Nat.Primrec fun _ => n | 0 => zero | n + 1 => Prim
rec.succ.comp (const n)  protected theorem id : Nat.Primrec id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const {n} : ∀ m, @Primrec' n fun _ => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0
  | m + 1 => succ.comp _ fun _ => const m
/-
**Nat.Primrec.head** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head {n : ℕ} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [get_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.Primrec.tail** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
/-
**Nat.Primrec.Vec** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from vectors to vectors is primitive recursive when all of its projec
tions are.
-/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get i
/-
**Nat.Primrec.nil** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0
/-
**Nat.Primrec.cons** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i
/-
**Nat.Primrec.idv** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idv {n} : @Vec n n id :=
  get
/-
**Nat.Primrec.comp'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp
/-
**Nat.Primrec.comp** 是 Mathlib 中的一个ctor，位于命名空间 `Nat.Primrec`。
形式化陈述：∀ {f g : ℕ → ℕ}, Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g
 n)
参数：g n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun _ => hg
/-
**Nat.Primrec.comp** 是 Mathlib 中的一个ctor，位于命名空间 `Nat.Primrec`。
形式化陈述：∀ {f g : ℕ → ℕ}, Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g
 n)
参数：g n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)
/-
**Nat.Primrec.prec'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)
/-
**Nat.Primrec.pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：pred : Nat.Primrec pred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem pred : @Primrec' 1 fun v => v.head.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl
/-
**Nat.Primrec.add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：add : Nat.Primrec (unpaired (· + ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
-/
theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]
/-
**Nat.Primrec.sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：sub : Nat.Primrec (unpaired (· - ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_add_eq`：∀ (a b c : ℕ), a - (b + c) = a - b - c
-/
theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
  have : @Primrec' 2 fun v ↦ (fun a b ↦ b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Nat.Primrec.mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：mul : Nat.Primrec (unpaired (· * ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.add`：add : Nat.Primrec (unpaired (· + ·))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]
/-
**Nat.Primrec.if_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]
/-
**Nat.Primrec.natPair** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))
/-
**Nat.Primrec.encode** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
  | _ + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl
/-
**Nat.Primrec.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
  suffices H : ∀ n : ℕ, n.sqrt =
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
        ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩
/-
**Nat.Primrec.unpair** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl
/-
**Nat.Primrec.unpair** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl
/-
**Nat.Primrec.of_prim** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_prim {n f} : Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector ℕ n) _ m).map f)
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
/-
**Nat.Primrec.prim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩
/-
**Nat.Primrec.prim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩
/-
**Nat.Primrec.prim_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩
/-
**Nat.Primrec.vec_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
    of_prim <| Primrec.vector_get.comp h (.const i)⟩

end Nat.Primrec'

/-
**Primrec.nat_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Primrec.nat_sqrt : Primrec Nat.sqrt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Primrec'.prim_iff₁`：prim_iff₁ {f : Nat -> Nat} : (@Primrec' 1 fun v 
=> f v.head) ↔ Primrec f
· 使用定理 `Nat.Primrec'.sqrt`：sqrt : @Primrec' 1 fun v => v.head.sqrt
-/
theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
