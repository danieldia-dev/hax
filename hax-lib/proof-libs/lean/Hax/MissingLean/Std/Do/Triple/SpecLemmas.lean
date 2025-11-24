import Std.Do.Triple.Basic
import Hax.MissingLean.Init.While
import Hax.MissingLean.Std.Do.PostCond

namespace Std.Do
open Lean

theorem Spec.forIn_monoloopCombinator {m} {ps : PostShape} {β: Type}
    [Monad m] [∀ α, Order.CCPO (m α)] [WPMonad m ps]
    (inv: β → Bool) (termination : β -> Nat) (init : β)
    (f : Unit → β → m (ForInStep β)) [Loop.MonoLoopCombinator f]
    (inv_init : inv init)
    (step : ∀ s,
      inv s →
      ⊢ₛ wp⟦do
          match ← f () s with
          | .yield s' => pure (inv s' ∧ termination s' < termination s)
          | .done s' => pure (inv s')
        ⟧
        ( ⇓ r => ⌜ r ⌝)) :
    ⊢ₛ wp⟦Loop.MonoLoopCombinator.forIn.loop f init⟧ (⇓ s' => ⌜ inv s' ⌝) := by
  apply SPred.entails.trans (step init inv_init)
  unfold Loop.MonoLoopCombinator.forIn.loop Loop.loopCombinator
  simp only [WP.bind]
  apply (wp (f () init)).mono _ _ (PostCond.entails.of_left_entails ?_)
  intro
  | .done a => simp
  | .yield a =>
    rw [WP.pure]
    apply SPred.pure_elim' fun h => forIn_monoloopCombinator inv termination a f h.1 step
termination_by termination init
decreasing_by exact h.2
