# algebraic-effects-montague

This repository contains the [Haskell](https://www.haskell.org/) code associated with the blog post *[Algebraic Effects in Montague Semantics](https://juliangrove.github.io/blog/algebraic_effects_montague.html)*.

The module [Fragment.hs](https://github.com/juliangrove/algebraic-effects-montague/blob/master/src/Fragment.hs) features some example sentences. One may do, for example,

	flip CMS.runState [] $ evalState $ handleSentence sentence3
	
which should be `False` and externally static. Or, one may do

	flip CMS.runState [] $ evalState $ handleSentence sentence5
	
which should be `False` and externally dynamic.
