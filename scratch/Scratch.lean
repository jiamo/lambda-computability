import Start.MartinLof

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ScratchNS

theorem test1 (T : Lambda.MLTest) :
    Computable fun z : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
      T.enter z.1.1.1 z.1.1.2 z.2.1 :=
  T.enter_computable.comp
    ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd)))

end ScratchNS
