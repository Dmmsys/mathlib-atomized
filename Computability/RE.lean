/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Computable and Recursively Enumerable Predicates

This file defines computable (`ComputablePred`) and recursively enumerable (`REPred`)
predicates. It also provides basic closure properties and Post's theorem on the
equivalence of recursive, r.e., and co-r.e. sets.
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

/-
**Nat.Partrec.merge'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) : exists h, Nat.Par
trec h ∧ forall a, (forall x in h a, x in f a ∨ x in g a) ∧ ((h a).Dom ↔ (f a).D
om ∨ (g a).Dom)
参数：hf : Nat.Partrec f；hg : Nat.Partrec g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Partrec.Code.exists_code`：exists_code {f : Nat ->. Nat} : Nat.Partre
c f ↔ exists c : Code, eval c = f
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Partrec.rfindOpt`：rfindOpt {f : α -> Nat -> Option σ} (hf : Computable₂ 
f) : Partrec fun a => Nat.rfindOpt (f a)
· 使用定理 `Computable₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Ty
pe u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable 
γ] [in…
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.option_orElse`：option_orElse : Primrec₂ ((· <|> ·) : Option α ->
 Option α -> Option α)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Nat.Partrec.Code.primrec_evaln`：primrec_evaln : Primrec fun a : (Nat × C
ode) × Nat => evaln a.1.1 a.1.2 a.2
· 使用定理 `Computable.pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {f : α → β} {
g : α…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Nat.rfindOpt_spec`：rfindOpt_spec {α} {f : Nat -> Option α} {a} (h : a in
 rfindOpt f) : exists n, a in f n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `Option.orElse_eq_some`：orElse_eq_some (o o' : Option α) (x : α) : (o <|>
 o') = some x ↔ o = some x ∨ o = none ∧ o' = some x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Partrec.Code.evaln_sound`：evaln_sound : forall {k c n x}, x in evaln
 k c n -> x in eval c n | 0, _, n, x, h => by simp [evaln] at h | k + 1, c, n, x
, h => by inductio…
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Nat.rfindOpt_dom`：rfindOpt_dom {α} {f : Nat -> Option α} : (rfindOpt f).
Dom ↔ exists n a, a in f n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 34 条，此处仅展示前 30 条）
-/
theorem merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) :
    ∃ h, Nat.Partrec h ∧
      ∀ a, (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧ ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
  have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n <|> cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cf)).pair fst)
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cg)).pair fst))
  refine ⟨_, this, fun n => ?_⟩
  have : ∀ x ∈ rfindOpt fun k ↦ Code.evaln k cf n <|> Code.evaln k cg n,
      x ∈ Code.eval cf n ∨ x ∈ Code.eval cg n := by
    intro x h
    obtain ⟨k, e⟩ := Nat.rfindOpt_spec h
    rw [Option.mem_def, Option.orElse_eq_some, ← Option.mem_def, ← Option.mem_def] at e
    obtain e | ⟨-, e⟩ := e <;> simp [Code.evaln_sound e]
  refine ⟨this, fun h ↦ (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, fun h ↦ ?_⟩
  rw [Nat.rfindOpt_dom]
  simp only [dom_iff_mem, Code.evaln_complete, Option.mem_def] at h
  obtain ⟨x, k, e⟩ | ⟨x, k, e⟩ := h
  · exact ⟨k, x, by simp [e]⟩
  · refine ⟨k, ?_⟩
    rcases cf.evaln k n with - | y
    · exact ⟨x, by simp [e]⟩
    · exact ⟨y, by simp⟩

end Nat.Partrec

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-
**Partrec.merge'** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：merge' {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g) : exists k : α ->
. σ, Partrec k ∧ forall a, (forall x in k a, x in f a ∨ x in g a) ∧ ((k a).Dom ↔
 (f a).Dom ∨ (g a).Dom)
参数：hf : Partrec f；hg : Partrec g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.merge'`：merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec 
g) : exists h, Nat.Partrec h ∧ forall a, (forall x in h a, x in f a ∨ x in g a) 
∧ ((h a)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Partrec.bind_decode₂_iff`：bind_decode₂_iff {f : α ->. σ} : Partrec f ↔ N
at.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Computable.encode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.encode
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Computable.ofOption`：ofOption {f : α -> Option β} (hf : Computable f) : 
Partrec fun a => (f a : Part β)
· 使用定理 `Computable.decode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.decode
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Encodable.decode₂_encode`：decode₂_encode [Encodable α] (a : α) : decode₂
 α (encode a) = some a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Part.bind_dom`：bind_dom {f : Part α} {g : α -> Part β} : (f.bind g).Dom 
↔ exists h : f.Dom, (g (f.get h)).Dom
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Encodable.encodek₂`：encodek₂ [Encodable α] (a : α) : decode₂ α (encode a
) = some a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem merge' {f g : α →. σ} (hf : Partrec f) (hg : Partrec g) :
    ∃ k : α →. σ,
      Partrec k ∧ ∀ a, (∀ x ∈ k a, x ∈ f a ∨ x ∈ g a) ∧ ((k a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have : ∀ x ∈ k' a, x ∈ f a ∨ x ∈ g a := by
    intro x h'
    simp only [k', mem_coe, mem_bind_iff, Option.mem_def] at h'
    obtain ⟨n, hn, hx⟩ := h'
    have := (H _).1 _ hn
    simp only [decode₂_encode, coe_some, bind_some, mem_map_iff] at this
    obtain ⟨a', ha, rfl⟩ | ⟨a', ha, rfl⟩ := this <;> simp only [encodek, Option.some_inj] at hx <;>
      rw [hx] at ha
    · exact Or.inl ha
    · exact Or.inr ha
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [bind_dom]
  have hk : (k (encode a)).Dom :=
    (H _).2.2 (by simpa only [encodek₂, bind_some, coe_some] using! h)
  exists hk
  simp only [mem_map_iff, mem_coe, mem_bind_iff, Option.mem_def] at H
  obtain ⟨a', _, y, _, e⟩ | ⟨a', _, y, _, e⟩ := (H _).1 _ ⟨hk, rfl⟩ <;>
    simp only [e.symm, encodek, coe_some, some_dom]
/-
**Partrec.merge** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：merge {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g) (H : forall (a), f
orall x in f a, forall y in g a, x = y) : exists k : α ->. σ, Partrec k ∧ forall
 a x, x in k a ↔ x in f a ∨ x in g a
参数：hf : Partrec f；hg : Partrec g；H : forall (a), forall x in f a, forall y in g 
a, x = y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.merge'`：merge' {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
 : exists k : α ->. σ, Partrec k ∧ forall a, (forall x in k a, x in f a ∨ x in g
 a) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem merge {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
    (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) :
    ∃ k : α →. σ, Partrec k ∧ ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a :=
  let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      rcases h with h | h <;> rcases (K _).1 _ ⟨this, rfl⟩ with h' | h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h').symm
      · exact H _ _ h' _ h
      · exact mem_unique h' h⟩⟩
/-
**Partrec.cond** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：cond {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Computable c) (hf :
 Partrec f) (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a)
参数：hc : Computable c；hf : Partrec f；hg : Partrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Partrec.Code.exists_code`：exists_code {f : Nat ->. Nat} : Nat.Partre
c f ↔ exists c : Code, eval c = f
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Nat.Partrec.Code.eval_part`：eval_part : Partrec₂ eval
· 使用定理 `Computable.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Co
mputable c) (hf : Computable f) (hg : Computable g) : Computable fun a => cond (
c a) …
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Computable.encode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.encode
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Computable.ofOption`：ofOption {f : α -> Option β} (hf : Computable f) : 
Partrec fun a => (f a : Part β)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.decode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.decode
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some_right`：bind_some_right (x : Part α) : x.bind some = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cond {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : Computable c) (hf : Partrec f)
    (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a) :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]

nonrec theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Partrec₂ h) : @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (sumCasesOn hf (const true).to₂ (const false).to₂)
          (sumCasesOn_left hf (option_some_iff.2 hg).to₂ (const Option.none).to₂)
          (sumCasesOn_right hf (const Option.none).to₂ (option_some_iff.2 hh).to₂)).of_eq
      fun a => by cases f a <;> simp only [Bool.cond_true, Bool.cond_false]

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
/-
**ComputablePred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ComputablePred {α} [Primcodable α] (p : α -> Prop)
参数：p : α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A computable predicate is one whose indicator function is computable.
-/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ (_ : DecidablePred p), Computable fun a => decide (p a)

section decide

variable {α} [Primcodable α]

/-
**ComputablePred.decide** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop} [inst_1 : Decidable
Pred p],   ComputablePred p → Computable fun a => decide (p a)
参数：p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected lemma ComputablePred.decide {p : α → Prop} [DecidablePred p] (hp : ComputablePred p) :
    Computable (fun a => decide (p a)) := by
  convert! hp.choose_spec
/-
**Computable.computablePred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Computable.computablePred {p : α -> Prop} [DecidablePred p] (hp : Computab
le (fun a => decide (p a))) : ComputablePred p
参数：hp : Computable (fun a => decide (p a))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Computable.computablePred {p : α → Prop} [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) : ComputablePred p :=
  ⟨inferInstance, hp⟩
/-
**computablePred_iff_computable_decide** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：computablePred_iff_computable_decide {p : α -> Prop} [DecidablePred p] : C
omputablePred p ↔ Computable (fun a => decide (p a)) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → 
Prop} [inst_1 : DecidablePred p],   ComputablePred p → Computable fun a => decid
e (p a)
· 使用引理 `Computable.computablePred`：Computable.computablePred {p : α -> Prop} [De
cidablePred p] (hp : Computable (fun a => decide (p a))) : ComputablePred p
-/
lemma computablePred_iff_computable_decide {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ Computable (fun a => decide (p a)) where
  mp := ComputablePred.decide
  mpr := Computable.computablePred
/-
**PrimrecPred.computablePred** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop}, PrimrecPred p → Co
mputablePred p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Computable.computablePred`：Computable.computablePred {p : α -> Prop} [De
cidablePred p] (hp : Computable (fun a => decide (p a))) : ComputablePred p
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
-/
lemma PrimrecPred.computablePred {α} [Primcodable α] {p : α → Prop} :
    (hp : PrimrecPred p) → ComputablePred p
  | ⟨_, hp⟩ => hp.to_comp.computablePred

end decide

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
-/
/-
**REPred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：REPred {α} [Primcodable α] (p : α -> Prop)
参数：p : α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursively enumerable predicate is one which is the domain of a computable pa
rtial function.
-/
def REPred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()
/-
**REPred.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：REPred.of_eq {α} [Primcodable α] {p q : α -> Prop} (hp : REPred p) (H : fo
rall a, p a ↔ q a) : REPred q
参数：hp : REPred p；H : forall a, p a ↔ q a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem REPred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (H : ∀ a, p a ↔ q a) :
    REPred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp
/-
**Partrec.dom_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α ->. β} (h : Pa
rtrec f) : REPred fun a => (f a).Dom
参数：h : Partrec f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) :
    REPred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]
/-
**ComputablePred.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ComputablePred.of_eq {α} [Primcodable α] {p q : α -> Prop} (hp : Computabl
ePred p) (H : forall a, p a ↔ q a) : ComputablePred q
参数：hp : ComputablePred p；H : forall a, p a ↔ q a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p)
    (H : ∀ a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace Computable

set_option backward.isDefEq.respectTransparency.types false in
/-- If `P` is computable, and if for every `x` there exists an `n` such that `P x n` holds,
then the function mapping `x` to the minimal such `n` (using `Nat.find`) is computable.
This formally bridges `Partrec.rfind` with total unbounded search. -/
/-
**Computable.find** 是 Mathlib 中的一个引理，位于命名空间 `Computable`。
形式化陈述：find {α : Type*} [Primcodable α] {P : α -> Nat -> Prop} [DecidableRel P] (
hP_comp : ComputablePred (fun p : α × Nat => P p.1 p.2)) (hP_ex : forall x, exis
ts n, P x n) : Computable (fun x => Nat.find (hP_ex x))
参数：hP_comp : ComputablePred (fun p : α × Nat => P p.1 p.2)；hP_ex : forall x, exi
sts n, P x n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.rfind`：rfind {p : α -> Nat ->. Bool} (hp : Partrec₂ p) : Partrec
 fun a => Nat.rfind (p a)
· 使用定理 `Computable.partrec`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable 
α] [inst_1 : Primcodable σ] {f : α → σ}, Computable f → Partrec ↑f
· 使用定理 `ComputablePred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → 
Prop} [inst_1 : DecidablePred p],   ComputablePred p → Computable fun a => decid
e (p a)
· 使用定理 `Partrec.of_eq_tot`：of_eq_tot {f : α ->. σ} {g : α -> σ} (hf : Partrec f)
 (H : forall n, g n in f n) : Computable g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `P` is computable, and if for every `x` there exists an `n` such that `P x n`
 holds,
then the function mapping `x` to the minimal such `n` (using `Nat.find`) is comp
utable.
This formally bridges `Partrec.rfind` with total unbounded search.
-/
lemma find {α : Type*} [Primcodable α] {P : α → ℕ → Prop} [DecidableRel P]
    (hP_comp : ComputablePred (fun p : α × ℕ => P p.1 p.2)) (hP_ex : ∀ x, ∃ n, P x n) :
    Computable (fun x => Nat.find (hP_ex x)) := by
  have h : Partrec (fun x ↦ Nat.rfind fun n => Part.some (decide (P x n))) :=
    Partrec.rfind hP_comp.decide.partrec
  refine h.of_eq_tot fun x ↦ ?_
  simp +contextual [Nat.find_spec]

end Computable

namespace ComputablePred

variable {α : Type*} [Primcodable α]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

/-
**ComputablePred.computable_iff** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：computable_iff {p : α -> Prop} : ComputablePred p ↔ exists f : α -> Bool, 
Computable f ∧ p = fun a => (f a : Prop)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Bool.decide_iff`：decide_iff (p : Prop) [d : Decidable p] : decide p = tr
ue ↔ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem computable_iff {p : α → Prop} :
    ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩
/-
**ComputablePred.not** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop}, ComputablePred p →
 ComputablePred fun a => ¬p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Computable.computablePred`：Computable.computablePred {p : α -> Prop} [De
cidablePred p] (hp : Computable (fun a => decide (p a))) : ComputablePred p
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.not`：Primrec not
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem not {p : α → Prop} :
    (hp : ComputablePred p) → ComputablePred fun a => ¬p a
  | ⟨_, hp⟩ => Computable.computablePred <| Primrec.not.to_comp.comp hp |>.of_eq <| by simp

/-- The computable functions are closed under if-then-else definitions
with computable predicates. -/
/-
**ComputablePred.ite** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：ite {f₁ f₂ : Nat -> Nat} (hf₁ : Computable f₁) (hf₂ : Computable f₂) {c : 
Nat -> Prop} [DecidablePred c] (hc : ComputablePred c) : Computable fun k => if 
c k then f₁ k else f₂ k
参数：hf₁ : Computable f₁；hf₂ : Computable f₂；hc : ComputablePred c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.cond_decide`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (t e 
: α), (bif decide p then t else e) = if p then t else e
· 使用定理 `Computable.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Co
mputable c) (hf : Computable f) (hg : Computable g) : Computable fun a => cond (
c a) …
· 使用定理 `ComputablePred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → 
Prop} [inst_1 : DecidablePred p],   ComputablePred p → Computable fun a => decid
e (p a)

--- 原说明 ---
The computable functions are closed under if-then-else definitions
with computable predicates.
-/
theorem ite {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
    {c : ℕ → Prop} [DecidablePred c] (hc : ComputablePred c) :
    Computable fun k ↦ if c k then f₁ k else f₂ k := by
  simpa [Bool.cond_decide] using hc.decide.cond hf₁ hf₂
/-
**ComputablePred.to_re** 是 Mathlib 中的一个定理，位于命名空间 `ComputablePred`。
形式化陈述：to_re {p : α -> Prop} (hp : ComputablePred p) : REPred p
参数：hp : ComputablePred p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ComputablePred.computable_iff`：computable_iff {p : α -> Prop} : Computab
lePred p ↔ exists f : α -> Bool, Computable f ∧ p = fun a => (f a : Prop)
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.cond`：cond {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Com
putable c) (hf : Partrec f) (hg : Partrec g) : Partrec fun a => cond (c a) (f a)
 (…
· 使用定理 `Decidable.Partrec.const'`：∀ {α : Type u_1} {σ : Type u_3} [inst : Primco
dable α] [inst_1 : Primcodable σ] (s : Part σ) [Decidable s.Dom],   Partrec fun 
x => s
· 使用定理 `Partrec.none`：none : Partrec fun _ : α => @Part.none σ
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem to_re {p : α → Prop} (hp : ComputablePred p) : REPred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

-- Post's theorem on the equivalence of r.e., co-r.e. sets and
-- computable sets. The assumption that p is decidable is required
-- unless we assume Markov's principle or LEM.
set_option linter.unusedDecidableInType false in
/-
**ComputablePred.computable_iff_re_compl_re** 是 Mathlib 中的一个定理，位于命名空间 `Computabl
ePred`。
形式化陈述：computable_iff_re_compl_re {p : α -> Prop} [DecidablePred p] : ComputableP
red p ↔ REPred p ∧ REPred fun a => ¬p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.to_re`：to_re {p : α -> Prop} (hp : ComputablePred p) : RE
Pred p
· 使用定理 `ComputablePred.not`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Pro
p}, ComputablePred p → ComputablePred fun a => ¬p a
· 使用定理 `Partrec.merge`：merge {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g) (
H : forall (a), forall x in f a, forall y in g a, x = y) : exists k : α ->. σ, P
art…
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
-/
theorem computable_iff_re_compl_re {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a :=
  ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop,
            and_true, exists_const] at hx hy
          cases hy.1 hx.1)
      refine Partrec.of_eq pk fun n => Part.eq_some_iff.2 ?_
      rw [hk]
      simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true,
        true_eq_decide_iff, and_self, exists_const, false_eq_decide_iff]
      apply Decidable.em⟩⟩
/-
**ComputablePred.computable_iff_re_compl_re'** 是 Mathlib 中的一个定理，位于命名空间 `Computab
lePred`。
形式化陈述：computable_iff_re_compl_re' {p : α -> Prop} : ComputablePred p ↔ REPred p 
∧ REPred fun a => ¬p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.computable_iff_re_compl_re`：computable_iff_re_compl_re {p
 : α -> Prop} [DecidablePred p] : ComputablePred p ↔ REPred p ∧ REPred fun a => 
¬p a
-/
theorem computable_iff_re_compl_re' {p : α → Prop} :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by
  classical exact computable_iff_re_compl_re

end ComputablePred

