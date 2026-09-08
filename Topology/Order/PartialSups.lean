/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Order.PartialSups

/-!
# Continuity of `partialSups`

In this file we prove that `partialSups` of a sequence of continuous functions is continuous
as well as versions for `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, and `ContinuousOn`.
-/

public section

open Filter
open scoped Topology

variable {L : Type*} [SemilatticeSup L] [TopologicalSpace L] [ContinuousSup L]

namespace Filter.Tendsto

variable {α : Type*} {l : Filter α} {f : ℕ → α → L} {g : ℕ → L} {n : ℕ}

/-
**Filter.Tendsto.partialSups** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {α : Type u_2} {l : Filter α}   {f : ℕ → α → L} {g : ℕ → L} {n 
: ℕ},   (∀ k ≤ n, Filter.Tendsto (f k) l (nhds (g k))) → Filter.Tendsto ((partia
lSups f) n) l (nhds ((partialSups g) n))
参数：∀ k ≤ n, Filter.Tendsto (f k) l (nhds (g k))；(partialSups f) n；nhds ((partial
Sups g) n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `partialSups_eq_sup'_range`：∀ {α : Type u_1} [inst : SemilatticeSup α] (f
 : ℕ → α) (n : ℕ), (partialSups f) n = (Finset.range (n + 1)).sup' ⋯ f
· 使用定理 `Filter.Tendsto.finset_sup'_nhds`：∀ {L : Type u_1} [inst : TopologicalSpa
ce L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Filter α
}   {g : ι → L} [inst…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected lemma partialSups (hf : ∀ k ≤ n, Tendsto (f k) l (𝓝 (g k))) :
    Tendsto (partialSups f n) l (𝓝 (partialSups g n)) := by
  simp only [partialSups_eq_sup'_range]
  refine finset_sup'_nhds _ ?_
  simpa [Nat.lt_succ_iff]
/-
**Filter.Tendsto.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {α : Type u_2} {l : Filter α}   {f : ℕ → α → L} {g : ℕ → L} {n 
: ℕ},   (∀ k ≤ n, Filter.Tendsto (f k) l (nhds (g k))) →     Filter.Tendsto (fun
 a => (partialSups fun x => f x a) n) l (nhds ((partialSups g) n))
参数：∀ k ≤ n, Filter.Tendsto (f k) l (nhds (g k))；fun a => (partialSups fun x => f
 x a) n；nhds ((partialSups g) n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.partialSups`：∀ {L : Type u_1} [inst : SemilatticeSup L] [
inst_1 : TopologicalSpace L] [ContinuousSup L] {α : Type u_2} {l : Filter α}   {
f : ℕ → α → L} {…
-/
protected lemma partialSups_apply (hf : ∀ k ≤ n, Tendsto (f k) l (𝓝 (g k))) :
    Tendsto (fun a ↦ partialSups (f · a) n) l (𝓝 (partialSups g n)) := by
  simpa only [← Pi.partialSups_apply] using Tendsto.partialSups hf

end Filter.Tendsto

variable {X : Type*} [TopologicalSpace X] {f : ℕ → X → L} {n : ℕ} {s : Set X} {x : X}

/-
**ContinuousAt.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {x : X},   (∀ k ≤ n, ContinuousAt (f k) x) → ContinuousAt (fun a => (par
tialSups fun x => f x a) n) x
参数：∀ k ≤ n, ContinuousAt (f k) x；fun a => (partialSups fun x => f x a) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.partialSups_apply`：∀ {L : Type u_1} [inst : SemilatticeSu
p L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {α : Type u_2} {l : Filter 
α}   {f : ℕ → α → L} {…
-/
protected lemma ContinuousAt.partialSups_apply (hf : ∀ k ≤ n, ContinuousAt (f k) x) :
    ContinuousAt (fun a ↦ partialSups (f · a) n) x :=
  Tendsto.partialSups_apply hf
/-
**ContinuousAt.partialSups** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {x : X},   (∀ k ≤ n, ContinuousAt (f k) x) → ContinuousAt ((partialSups 
f) n) x
参数：∀ k ≤ n, ContinuousAt (f k) x；(partialSups f) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAt.partialSups_apply`：∀ {L : Type u_1} [inst : SemilatticeSup 
L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_3 : To
pologicalSpace X] {f…
-/
protected lemma ContinuousAt.partialSups (hf : ∀ k ≤ n, ContinuousAt (f k) x) :
    ContinuousAt (partialSups f n) x := by
  simpa only [← Pi.partialSups_apply] using ContinuousAt.partialSups_apply hf
/-
**ContinuousWithinAt.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWith
inAt`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {s : Set X} {x : X},   (∀ k ≤ n, ContinuousWithinAt (f k) s x) → Continu
ousWithinAt (fun a => (partialSups fun x => f x a) n) s x
参数：∀ k ≤ n, ContinuousWithinAt (f k) s x；fun a => (partialSups fun x => f x a) n
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.partialSups_apply`：∀ {L : Type u_1} [inst : SemilatticeSu
p L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {α : Type u_2} {l : Filter 
α}   {f : ℕ → α → L} {…
-/
protected lemma ContinuousWithinAt.partialSups_apply (hf : ∀ k ≤ n, ContinuousWithinAt (f k) s x) :
    ContinuousWithinAt (fun a ↦ partialSups (f · a) n) s x :=
  Tendsto.partialSups_apply hf
/-
**ContinuousWithinAt.partialSups** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWithinAt`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {s : Set X} {x : X},   (∀ k ≤ n, ContinuousWithinAt (f k) s x) → Continu
ousWithinAt ((partialSups f) n) s x
参数：∀ k ≤ n, ContinuousWithinAt (f k) s x；(partialSups f) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousWithinAt.partialSups_apply`：∀ {L : Type u_1} [inst : Semilatti
ceSup L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_
3 : TopologicalSpace X] {f…
-/
protected lemma ContinuousWithinAt.partialSups (hf : ∀ k ≤ n, ContinuousWithinAt (f k) s x) :
    ContinuousWithinAt (partialSups f n) s x := by
  simpa only [← Pi.partialSups_apply] using ContinuousWithinAt.partialSups_apply hf
/-
**ContinuousOn.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {s : Set X},   (∀ k ≤ n, ContinuousOn (f k) s) → ContinuousOn (fun a => 
(partialSups fun x => f x a) n) s
参数：∀ k ≤ n, ContinuousOn (f k) s；fun a => (partialSups fun x => f x a) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.partialSups_apply`：∀ {L : Type u_1} [inst : Semilatti
ceSup L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_
3 : TopologicalSpace X] {f…
-/
protected lemma ContinuousOn.partialSups_apply (hf : ∀ k ≤ n, ContinuousOn (f k) s) :
    ContinuousOn (fun a ↦ partialSups (f · a) n) s := fun x hx ↦
  ContinuousWithinAt.partialSups_apply fun k hk ↦ hf k hk x hx
/-
**ContinuousOn.partialSups** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ} {s : Set X},   (∀ k ≤ n, ContinuousOn (f k) s) → ContinuousOn ((partialS
ups f) n) s
参数：∀ k ≤ n, ContinuousOn (f k) s；(partialSups f) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.partialSups`：∀ {L : Type u_1} [inst : SemilatticeSup 
L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_3 : To
pologicalSpace X] {f…
-/
protected lemma ContinuousOn.partialSups (hf : ∀ k ≤ n, ContinuousOn (f k) s) :
    ContinuousOn (partialSups f n) s := fun x hx ↦
  ContinuousWithinAt.partialSups fun k hk ↦ hf k hk x hx
/-
**Continuous.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ},   (∀ k ≤ n, Continuous (f k)) → Continuous fun a => (partialSups fun x 
=> f x a) n
参数：∀ k ≤ n, Continuous (f k)；partialSups fun x => f x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.partialSups_apply`：∀ {L : Type u_1} [inst : SemilatticeSup 
L] [inst_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_3 : To
pologicalSpace X] {f…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
protected lemma Continuous.partialSups_apply (hf : ∀ k ≤ n, Continuous (f k)) :
    Continuous (fun a ↦ partialSups (f · a) n) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.partialSups_apply fun k hk ↦
    (hf k hk).continuousAt
/-
**Continuous.partialSups** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {L : Type u_1} [inst : SemilatticeSup L] [inst_1 : TopologicalSpace L] [
ContinuousSup L] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f : ℕ → X → L} 
{n : ℕ}, (∀ k ≤ n, Continuous (f k)) → Continuous ((partialSups f) n)
参数：∀ k ≤ n, Continuous (f k)；(partialSups f) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.partialSups`：∀ {L : Type u_1} [inst : SemilatticeSup L] [in
st_1 : TopologicalSpace L] [ContinuousSup L] {X : Type u_2}   [inst_3 : Topologi
calSpace X] {f…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
protected lemma Continuous.partialSups (hf : ∀ k ≤ n, Continuous (f k)) :
    Continuous (partialSups f n) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.partialSups fun k hk ↦ (hf k hk).continuousAt
