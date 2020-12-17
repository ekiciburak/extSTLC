Imports.vo Imports.glob Imports.v.beautified: Imports.v
Imports.vio: Imports.v
Terms.vo Terms.glob Terms.v.beautified: Terms.v Imports.vo Auxiliaries.vo
Terms.vio: Terms.v Imports.vio Auxiliaries.vio
Auxiliaries.vo Auxiliaries.glob Auxiliaries.v.beautified: Auxiliaries.v Imports.vo
Auxiliaries.vio: Auxiliaries.v Imports.vio
Typecheck.vo Typecheck.glob Typecheck.v.beautified: Typecheck.v Imports.vo Auxiliaries.vo Terms.vo
Typecheck.vio: Typecheck.v Imports.vio Auxiliaries.vio Terms.vio
Eval.vo Eval.glob Eval.v.beautified: Eval.v Imports.vo Terms.vo Auxiliaries.vo Typecheck.vo
Eval.vio: Eval.v Imports.vio Terms.vio Auxiliaries.vio Typecheck.vio
Progress.vo Progress.glob Progress.v.beautified: Progress.v Imports.vo Terms.vo Auxiliaries.vo Typecheck.vo Eval.vo
Progress.vio: Progress.v Imports.vio Terms.vio Auxiliaries.vio Typecheck.vio Eval.vio
Preservation.vo Preservation.glob Preservation.v.beautified: Preservation.v Imports.vo Terms.vo Auxiliaries.vo Typecheck.vo Eval.vo Progress.vo
Preservation.vio: Preservation.v Imports.vio Terms.vio Auxiliaries.vio Typecheck.vio Eval.vio Progress.vio
Stlc_sound.vo Stlc_sound.glob Stlc_sound.v.beautified: Stlc_sound.v Imports.vo Auxiliaries.vo Terms.vo Typecheck.vo Eval.vo Progress.vo Preservation.vo
Stlc_sound.vio: Stlc_sound.v Imports.vio Auxiliaries.vio Terms.vio Typecheck.vio Eval.vio Progress.vio Preservation.vio
