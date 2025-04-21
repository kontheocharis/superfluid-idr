module Core.Substitution

import Common
import Context
import Core.Values

public export
interface Subst (0 sub : Named (Named Type)) (0 tm : Named Type) | tm where
  -- Required
  id : Size gs -> sub gs gs
  term : Size gs -> sub gs [<]
  compose : sub gs hs -> sub is gs -> sub is hs
  ext : sub gs hs -> tm gs -> sub gs (hs :< h)
  proj : sub gs (hs :< h) -> sub gs hs
  res : tm gs -> sub hs gs -> tm hs
  take : (s : sub gs (hs :< h)) -> tm gs
  build : Spine tm hs gs -> sub gs hs

  -- Defaults
  wk : Size hs -> sub (hs :< h) hs
  wk sz @{s} = proj @{s} (id @{s} (SS sz))

  weak : Size gs -> tm gs -> tm (gs :< g)
  weak sz @{s} t = res t (wk @{s} sz)

  -- resSp : Spine tm ps gs -> sub hs gs -> Spine tm ps hs
  -- resSp [<] s = [<]
  -- resSp (ts :< t) s = (resSp ts s :< res t s)

  wkN : Size hs -> Size by -> sub (hs ++ by) hs
  wkN sz SZ @{s} = id @{s} sz
  wkN sz (SS by) @{s} = compose @{s} (wkN sz by @{s}) (wk @{s} (sz + by))

  wkN2 : Size hs -> Size by -> Size cy -> sub ((hs ++ by) ++ cy) hs
  wkN2 sz by cy @{s} = compose @{s} (wkN sz by @{s}) (wkN (sz + by) cy @{s})

  join : Size is -> sub gs hs -> sub gs is -> sub gs (hs ++ is)
  join @{s} SZ s1 s2 = s1
  join @{s} (SS is) s1 s2 = ext @{s} (join @{s} is s1 (proj @{s} s2)) (take s2)

  takeN : sub gs (hs ++ is) -> Spine tm is gs

  plug : Size gs -> tm (gs :< g) -> tm gs -> tm gs
  plug @{s} gsSize t u = res t (ext @{s} (id @{s} gsSize) u)

  plugN : Size gs -> tm (gs ++ hs) -> Spine tm hs gs -> tm gs
  plugN @{s} gsSize t sp = res t (join @{s} sp.size (id @{s} gsSize) (build sp))

  anyBaseN : tm (gs ++ ps) -> forall gs' . tm ((gs ++ gs') ++ ps)
  anyBaseN @{s} t = res t ?fa
