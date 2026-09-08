/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
### Continuity of piecewise defined functions
-/

public section

open Set Filter Function Topology Filter

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  {f g : α → β} {s s' t : Set α} {x : α}


@[simp]
/-
**continuousWithinAt_update_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_update_same [DecidableEq α] {y : β} : ContinuousWithinA
t (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_sdiff_self`：continuousWithinAt_sdiff_self : Continuou
sWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousWithinAt_update_same [DecidableEq α] {y : β} :
    ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
  calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
    { rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, update_self] }
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
      tendsto_congr' <| eventually_nhdsWithin_iff.2 <| Eventually.of_forall
        fun _ hz => update_of_ne hz.2 ..

@[simp]
/-
**continuousAt_update_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_update_same [DecidableEq α] {y : β} : ContinuousAt (Function.
update f x y) x ↔ Tendsto f (𝓝[!=] x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `continuousWithinAt_update_same`：continuousWithinAt_update_same [Decidabl
eEq α] {y : β} : ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x
) (𝓝 y)
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_update_same [DecidableEq α] {y : β} :
    ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[≠] x) (𝓝 y) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_update_same, compl_eq_univ_sdiff]
/-
**ContinuousOn.if'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.if' {s : Set α} {p : α -> Prop} {f g : α -> β} [forall a, Dec
idable (p a)] (hpf : forall a in s inter frontier { a | p a }, Tendsto f (𝓝[s in
ter { a | p a }] a) (𝓝 <| if p a then f a else g a)) (hpg : forall a in s inter 
frontier { a | p a }, Tendsto g (𝓝[s inter { a | ¬p a }] a) (𝓝 <| if p a then f 
a else g a)) (hf : ContinuousOn f <| s inter { a | p a }) (hg : ContinuousOn g <
| s inter { a | ¬p a }) : ContinuousOn (fun a => if p a then f a else g a) s
参数：p a；hpf : forall a in s inter frontier { a | p a }, Tendsto f (𝓝[s inter { a 
| p a }] a) (𝓝 <| if p a then f a else g a)；hpg : forall a in s inter frontier {
 a | p a }, Tendsto g (𝓝[s inter { a | ¬p a }] a) (𝓝 <| if p a then f a else g a
)；hf : ContinuousOn f <| s inter { a | p a }；hg : ContinuousOn g <| s inter { a 
| ¬p a }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.piecewise_nhdsWithin`：Filter.Tendsto.piecewise_nhdsWithin
 {f g : α -> β} {t : Set α} [forall x, Decidable (x in t)] {a : α} {s : Set α} {
l : Filter β} (h₀ : Tends…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `ContinuousWithinAt.union`：ContinuousWithinAt.union (hs : ContinuousWithi
nAt f s x) (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s union t) x
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `continuousWithinAt_of_notMem_closure`：continuousWithinAt_of_notMem_closu
re (hx : x ∉ closure s) : ContinuousWithinAt f s x
· 使用定理 `closure_inter_subset_inter_closure`：closure_inter_subset_inter_closure (
s t : Set X) : closure (s inter t) subseteq closure s inter closure t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem ContinuousOn.if' {s : Set α} {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hpf : ∀ a ∈ s ∩ frontier { a | p a },
      Tendsto f (𝓝[s ∩ { a | p a }] a) (𝓝 <| if p a then f a else g a))
    (hpg :
      ∀ a ∈ s ∩ frontier { a | p a },
        Tendsto g (𝓝[s ∩ { a | ¬p a }] a) (𝓝 <| if p a then f a else g a))
    (hf : ContinuousOn f <| s ∩ { a | p a }) (hg : ContinuousOn g <| s ∩ { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s := by
  intro x hx
  by_cases hx' : x ∈ frontier { a | p a }
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhdsWithin (hpg x ⟨hx, hx'⟩)
  · rw [← inter_univ s, ← union_compl_self { a | p a }, inter_union_distrib_left] at hx ⊢
    rcases hx with hx | hx
    · apply ContinuousWithinAt.union
      · exact (hf x hx).congr (fun y hy => if_pos hy.2) (if_pos hx.2)
      · have : x ∉ closure { a | p a }ᶜ := fun h => hx' ⟨subset_closure hx.2, by
          rwa [closure_compl] at h⟩
        exact continuousWithinAt_of_notMem_closure fun h =>
          this (closure_inter_subset_inter_closure _ _ h).2
    · apply ContinuousWithinAt.union
      · have : x ∉ closure { a | p a } := fun h =>
          hx' ⟨h, fun h' : x ∈ interior { a | p a } => hx.2 (interior_subset h')⟩
        exact continuousWithinAt_of_notMem_closure fun h =>
          this (closure_inter_subset_inter_closure _ _ h).2
      · exact (hg x hx).congr (fun y hy => if_neg hy.2) (if_neg hx.2)
/-
**ContinuousOn.piecewise'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.piecewise' [forall a, Decidable (a in t)] (hpf : forall a in 
s inter frontier t, Tendsto f (𝓝[s inter t] a) (𝓝 (piecewise t f g a))) (hpg : f
orall a in s inter frontier t, Tendsto g (𝓝[s inter tᶜ] a) (𝓝 (piecewise t f g a
))) (hf : ContinuousOn f <| s inter t) (hg : ContinuousOn g <| s inter tᶜ) : Con
tinuousOn (piecewise t f g) s
参数：a in t；hpf : forall a in s inter frontier t, Tendsto f (𝓝[s inter t] a) (𝓝 (p
iecewise t f g a))；hpg : forall a in s inter frontier t, Tendsto g (𝓝[s inter tᶜ
] a) (𝓝 (piecewise t f g a))；hf : ContinuousOn f <| s inter t；hg : ContinuousOn 
g <| s inter tᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.if'`：ContinuousOn.if' {s : Set α} {p : α -> Prop} {f g : α 
-> β} [forall a, Decidable (p a)] (hpf : forall a in s inter frontier { a | p a 
}, Ten…
-/
theorem ContinuousOn.piecewise' [∀ a, Decidable (a ∈ t)]
    (hpf : ∀ a ∈ s ∩ frontier t, Tendsto f (𝓝[s ∩ t] a) (𝓝 (piecewise t f g a)))
    (hpg : ∀ a ∈ s ∩ frontier t, Tendsto g (𝓝[s ∩ tᶜ] a) (𝓝 (piecewise t f g a)))
    (hf : ContinuousOn f <| s ∩ t) (hg : ContinuousOn g <| s ∩ tᶜ) :
    ContinuousOn (piecewise t f g) s :=
  hf.if' hpf hpg hg
/-
**ContinuousOn.if** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.if {p : α -> Prop} [forall a, Decidable (p a)] (hp : forall a
 in s inter frontier { a | p a }, f a = g a) (hf : ContinuousOn f <| s inter clo
sure { a | p a }) (hg : ContinuousOn g <| s inter closure { a | ¬p a }) : Contin
uousOn (fun a => if p a then f a else g a) s
参数：p a；hp : forall a in s inter frontier { a | p a }, f a = g a；hf : ContinuousO
n f <| s inter closure { a | p a }；hg : ContinuousOn g <| s inter closure { a | 
¬p a }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.if'`：ContinuousOn.if' {s : Set α} {p : α -> Prop} {f g : α 
-> β} [forall a, Decidable (p a)] (hpf : forall a in s inter frontier { a | p a 
}, Ten…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `tendsto_nhdsWithin_mono_left`：tendsto_nhdsWithin_mono_left {f : α -> β} 
{a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t) (h : Tendsto f (𝓝[t] a
) l) : Tendsto f (…
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem ContinuousOn.if {p : α → Prop} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ s ∩ frontier { a | p a }, f a = g a)
    (hf : ContinuousOn f <| s ∩ closure { a | p a })
    (hg : ContinuousOn g <| s ∩ closure { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s := by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [← hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
  · rintro a ha
    simp only [hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    rcases ha with ⟨has, ⟨_, ha⟩⟩
    rw [← mem_compl_iff, ← closure_compl] at ha
    apply hg a ⟨has, ha⟩
  · exact hf.mono (inter_subset_inter_right s subset_closure)
  · exact hg.mono (inter_subset_inter_right s subset_closure)
/-
**ContinuousOn.piecewise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.piecewise [forall a, Decidable (a in t)] (ht : forall a in s 
inter frontier t, f a = g a) (hf : ContinuousOn f <| s inter closure t) (hg : Co
ntinuousOn g <| s inter closure tᶜ) : ContinuousOn (piecewise t f g) s
参数：a in t；ht : forall a in s inter frontier t, f a = g a；hf : ContinuousOn f <| 
s inter closure t；hg : ContinuousOn g <| s inter closure tᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.if`：ContinuousOn.if {p : α -> Prop} [forall a, Decidable (p
 a)] (hp : forall a in s inter frontier { a | p a }, f a = g a) (hf : Continuous
On f …
-/
theorem ContinuousOn.piecewise [∀ a, Decidable (a ∈ t)]
    (ht : ∀ a ∈ s ∩ frontier t, f a = g a) (hf : ContinuousOn f <| s ∩ closure t)
    (hg : ContinuousOn g <| s ∩ closure tᶜ) : ContinuousOn (piecewise t f g) s :=
  hf.if ht hg
/-
**continuous_if'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_if' {p : α -> Prop} [forall a, Decidable (p a)] (hpf : forall a
 in frontier { x | p x }, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <| ite (p a) (f a) (g 
a))) (hpg : forall a in frontier { x | p x }, Tendsto g (𝓝[{ x | ¬p x }] a) (𝓝 <
| ite (p a) (f a) (g a))) (hf : ContinuousOn f { x | p x }) (hg : ContinuousOn g
 { x | ¬p x }) : Continuous fun a => ite (p a) (f a) (g a)
参数：p a；hpf : forall a in frontier { x | p x }, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <
| ite (p a) (f a) (g a))；hpg : forall a in frontier { x | p x }, Tendsto g (𝓝[{ 
x | ¬p x }] a) (𝓝 <| ite (p a) (f a) (g a))；hf : ContinuousOn f { x | p x }；hg :
 ContinuousOn g { x | ¬p x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.if'`：ContinuousOn.if' {s : Set α} {p : α -> Prop} {f g : α 
-> β} [forall a, Decidable (p a)] (hpf : forall a in s inter frontier { a | p a 
}, Ten…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem continuous_if' {p : α → Prop} [∀ a, Decidable (p a)]
    (hpf : ∀ a ∈ frontier { x | p x }, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hpg : ∀ a ∈ frontier { x | p x }, Tendsto g (𝓝[{ x | ¬p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hf : ContinuousOn f { x | p x }) (hg : ContinuousOn g { x | ¬p x }) :
    Continuous fun a => ite (p a) (f a) (g a) := by
  rw [← continuousOn_univ]
  apply ContinuousOn.if' <;> simpa
/-
**continuous_if** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_if {p : α -> Prop} [forall a, Decidable (p a)] (hp : forall a i
n frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closure { x | p x })) (
hg : ContinuousOn g (closure { x | ¬p x })) : Continuous fun a => if p a then f 
a else g a
参数：p a；hp : forall a in frontier { x | p x }, f a = g a；hf : ContinuousOn f (clo
sure { x | p x })；hg : ContinuousOn g (closure { x | ¬p x })。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.if`：ContinuousOn.if {p : α -> Prop} [forall a, Decidable (p
 a)] (hp : forall a in s inter frontier { a | p a }, f a = g a) (hf : Continuous
On f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem continuous_if {p : α → Prop} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closure { x | p x }))
    (hg : ContinuousOn g (closure { x | ¬p x })) :
    Continuous fun a => if p a then f a else g a := by
  rw [← continuousOn_univ]
  apply ContinuousOn.if <;> simpa
/-
**Continuous.if** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.if {p : α -> Prop} [forall a, Decidable (p a)] (hp : forall a i
n frontier { x | p x }, f a = g a) (hf : Continuous f) (hg : Continuous g) : Con
tinuous fun a => if p a then f a else g a
参数：p a；hp : forall a in frontier { x | p x }, f a = g a；hf : Continuous f；hg : C
ontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if`：continuous_if {p : α -> Prop} [forall a, Decidable (p a)]
 (hp : forall a in frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closur
e {…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.if {p : α → Prop} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ frontier { x | p x }, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => if p a then f a else g a :=
  continuous_if hp hf.continuousOn hg.continuousOn
/-
**continuous_if_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_if_const (p : Prop) [Decidable p] (hf : p -> Continuous f) (hg 
: ¬p -> Continuous g) : Continuous fun a => if p then f a else g a
参数：p : Prop；hf : p -> Continuous f；hg : ¬p -> Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem continuous_if_const (p : Prop) [Decidable p] (hf : p → Continuous f)
    (hg : ¬p → Continuous g) : Continuous fun a => if p then f a else g a := by
  split_ifs with h
  exacts [hf h, hg h]
/-
**Continuous.if_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.if_const (p : Prop) [Decidable p] (hf : Continuous f) (hg : Con
tinuous g) : Continuous fun a => if p then f a else g a
参数：p : Prop；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if_const`：continuous_if_const (p : Prop) [Decidable p] (hf : 
p -> Continuous f) (hg : ¬p -> Continuous g) : Continuous fun a => if p then f a
 else g a
-/
theorem Continuous.if_const (p : Prop) [Decidable p] (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => if p then f a else g a :=
  continuous_if_const p (fun _ => hf) fun _ => hg
/-
**continuous_piecewise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_piecewise [forall a, Decidable (a in s)] (hs : forall a in fron
tier s, f a = g a) (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closu
re sᶜ)) : Continuous (piecewise s f g)
参数：a in s；hs : forall a in frontier s, f a = g a；hf : ContinuousOn f (closure s)
；hg : ContinuousOn g (closure sᶜ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if`：continuous_if {p : α -> Prop} [forall a, Decidable (p a)]
 (hp : forall a in frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closur
e {…
-/
theorem continuous_piecewise [∀ a, Decidable (a ∈ s)]
    (hs : ∀ a ∈ frontier s, f a = g a) (hf : ContinuousOn f (closure s))
    (hg : ContinuousOn g (closure sᶜ)) : Continuous (piecewise s f g) :=
  continuous_if hs hf hg
/-
**Continuous.piecewise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.piecewise [forall a, Decidable (a in s)] (hs : forall a in fron
tier s, f a = g a) (hf : Continuous f) (hg : Continuous g) : Continuous (piecewi
se s f g)
参数：a in s；hs : forall a in frontier s, f a = g a；hf : Continuous f；hg : Continuo
us g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.if`：Continuous.if {p : α -> Prop} [forall a, Decidable (p a)]
 (hp : forall a in frontier { x | p x }, f a = g a) (hf : Continuous f) (hg : Co
nti…
-/
theorem Continuous.piecewise [∀ a, Decidable (a ∈ s)]
    (hs : ∀ a ∈ frontier s, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous (piecewise s f g) :=
  hf.if hs hg
/-
**IsOpen.ite'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.ite' (hs : IsOpen s) (hs' : IsOpen s') (ht : forall x in frontier t
, x in s ↔ x in s') : IsOpen (t.ite s s')
参数：hs : IsOpen s；hs' : IsOpen s'；ht : forall x in frontier t, x in s ↔ x in s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `continuous_piecewise`：continuous_piecewise [forall a, Decidable (a in s)
] (hs : forall a in frontier s, f a = g a) (hf : ContinuousOn f (closure s)) (hg
 : Continu…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem IsOpen.ite' (hs : IsOpen s) (hs' : IsOpen s')
    (ht : ∀ x ∈ frontier t, x ∈ s ↔ x ∈ s') : IsOpen (t.ite s s') := by
  classical
    simp only [isOpen_iff_continuous_mem, Set.ite] at *
    convert!
      continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuousOn hs'.continuousOn using 2
    rename_i x
    by_cases hx : x ∈ t <;> simp [hx]
/-
**IsOpen.ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.ite (hs : IsOpen s) (hs' : IsOpen s') (ht : s inter frontier t = s'
 inter frontier t) : IsOpen (t.ite s s')
参数：hs : IsOpen s；hs' : IsOpen s'；ht : s inter frontier t = s' inter frontier t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.ite'`：IsOpen.ite' (hs : IsOpen s) (hs' : IsOpen s') (ht : forall 
x in frontier t, x in s ↔ x in s') : IsOpen (t.ite s s')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem IsOpen.ite (hs : IsOpen s) (hs' : IsOpen s')
    (ht : s ∩ frontier t = s' ∩ frontier t) : IsOpen (t.ite s s') :=
  hs.ite' hs' fun x hx => by simpa [hx] using Set.ext_iff.1 ht x
/-
**ite_inter_closure_eq_of_inter_frontier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_inter_closure_eq_of_inter_frontier_eq (ht : s inter frontier t = s' in
ter frontier t) : t.ite s s' inter closure t = s inter closure t
参数：ht : s inter frontier t = s' inter frontier t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_self_union_frontier`：closure_eq_self_union_frontier (s : Set 
X) : closure s = s union frontier s
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.ite_inter_self`：ite_inter_self (t s s' : Set α) : t.ite s s' inter t
 = s inter t
· 使用定理 `Set.ite_inter_of_inter_eq`：ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : 
Set α} (h : s₁ inter s = s₂ inter s) : t.ite s₁ s₂ inter s = s₁ inter s
-/
theorem ite_inter_closure_eq_of_inter_frontier_eq
    (ht : s ∩ frontier t = s' ∩ frontier t) : t.ite s s' ∩ closure t = s ∩ closure t := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_union_distrib_left,
    ite_inter_self, ite_inter_of_inter_eq _ ht]
/-
**ite_inter_closure_compl_eq_of_inter_frontier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_inter_closure_compl_eq_of_inter_frontier_eq (ht : s inter frontier t =
 s' inter frontier t) : t.ite s s' inter closure tᶜ = s' inter closure tᶜ
参数：ht : s inter frontier t = s' inter frontier t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ite_compl`：ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s
· 使用定理 `ite_inter_closure_eq_of_inter_frontier_eq`：ite_inter_closure_eq_of_inter
_frontier_eq (ht : s inter frontier t = s' inter frontier t) : t.ite s s' inter 
closure t = s inter closure t
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem ite_inter_closure_compl_eq_of_inter_frontier_eq
    (ht : s ∩ frontier t = s' ∩ frontier t) : t.ite s s' ∩ closure tᶜ = s' ∩ closure tᶜ := by
  rw [← ite_compl, ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]
/-
**continuousOn_piecewise_ite'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_piecewise_ite' [forall x, Decidable (x in t)] (h : Continuous
On f (s inter closure t)) (h' : ContinuousOn g (s' inter closure tᶜ)) (H : s int
er frontier t = s' inter frontier t) (Heq : EqOn f g (s inter frontier t)) : Con
tinuousOn (t.piecewise f g) (t.ite s s')
参数：x in t；h : ContinuousOn f (s inter closure t)；h' : ContinuousOn g (s' inter c
losure tᶜ)；H : s inter frontier t = s' inter frontier t；Heq : EqOn f g (s inter 
frontier t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.piecewise`：ContinuousOn.piecewise [forall a, Decidable (a i
n t)] (ht : forall a in s inter frontier t, f a = g a) (hf : ContinuousOn f <| s
 inter closu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ite_inter_of_inter_eq`：ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : 
Set α} (h : s₁ inter s = s₂ inter s) : t.ite s₁ s₂ inter s = s₁ inter s
· 使用定理 `ite_inter_closure_eq_of_inter_frontier_eq`：ite_inter_closure_eq_of_inter
_frontier_eq (ht : s inter frontier t = s' inter frontier t) : t.ite s s' inter 
closure t = s inter closure t
· 使用定理 `ite_inter_closure_compl_eq_of_inter_frontier_eq`：ite_inter_closure_compl
_eq_of_inter_frontier_eq (ht : s inter frontier t = s' inter frontier t) : t.ite
 s s' inter closure tᶜ = s' inter clo…
-/
theorem continuousOn_piecewise_ite' [∀ x, Decidable (x ∈ t)]
    (h : ContinuousOn f (s ∩ closure t)) (h' : ContinuousOn g (s' ∩ closure tᶜ))
    (H : s ∩ frontier t = s' ∩ frontier t) (Heq : EqOn f g (s ∩ frontier t)) :
    ContinuousOn (t.piecewise f g) (t.ite s s') := by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]
/-
**continuousOn_piecewise_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_piecewise_ite [forall x, Decidable (x in t)] (h : ContinuousO
n f s) (h' : ContinuousOn g s') (H : s inter frontier t = s' inter frontier t) (
Heq : EqOn f g (s inter frontier t)) : ContinuousOn (t.piecewise f g) (t.ite s s
')
参数：x in t；h : ContinuousOn f s；h' : ContinuousOn g s'；H : s inter frontier t = s
' inter frontier t；Heq : EqOn f g (s inter frontier t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_piecewise_ite'`：continuousOn_piecewise_ite' [forall x, Deci
dable (x in t)] (h : ContinuousOn f (s inter closure t)) (h' : ContinuousOn g (s
' inter closure t…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem continuousOn_piecewise_ite [∀ x, Decidable (x ∈ t)]
    (h : ContinuousOn f s) (h' : ContinuousOn g s') (H : s ∩ frontier t = s' ∩ frontier t)
    (Heq : EqOn f g (s ∩ frontier t)) : ContinuousOn (t.piecewise f g) (t.ite s s') :=
  continuousOn_piecewise_ite' (h.mono inter_subset_left) (h'.mono inter_subset_left) H Heq
