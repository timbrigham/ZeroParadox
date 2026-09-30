"""
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 3.45 | September 2026
v3.45: LANE B, REMARK R-eps0 (DEFECTS.md ZPE-EPS0-MISDESCRIBED AR3-7 and AR3-8, PRIOR-ART-DB-ORDINARY PA-6a; Tim ruling 2026-09-30). AR3-7: the remark said eps0 in Step 6 'denotes the minimum element of L strictly above bottom', which needs a unique least element that A1-A4 and AX-B1 do not give (Set Bool has two first steps and no least one; a dense L has none); it now names an element Step 6 asserts to exist and says where it is least, and 'minimum' is dropped from the title and three dependent sentences. AR3-8: 'the minimum ordinal that cannot be generated from 0 by any finite iteration' was false (2 lies below eps0 and on no tower stage); the clause is deleted, and the least-fixed-point and supremum faces beside it stand. PA-6a: the coinage 'Cantor-Gentzen' is replaced at its three rendered sites. Measuring examples: ZeroParadox/Reals/OrderedField.lean and ZeroParadox/Ordinal/Gentzen.lean (437623f).
v3.44: A PREMISE ASSERTING THAT ZF + AFA SPECIFICALLY IS FORCED, CARRYING THE REMARK'S CONCLUSION, IN AN ALREADY-DEPOSITED PDF - AND THE SUPERLATIVE AND THE CITATIONS THAT STOOD BESIDE IT (DEFECTS.md PRIOR-ART-DB-ORDINARY finding PA-3 and ADV-ZPE-PA2 findings AR-F1 to AR-F4; prior_art gate 2026-09-15, editorial EO-1 2026-09-26, adversary round 2 2026-09-27; editorial round 1 of this arc, 2026-09-27, FAIL-BEDROCK, findings B1 and F2 to F9, note .claude-local/notes/editorial_review_2026-09-27_zpe-pa3.md). (1) B1, BEDROCK, FOUR RENDERED SITES WRITTEN FROM THREE SOURCE STRINGS, AND THIS DOCUMENT WAS THE ONLY SURFACE IN THE CORPUS STILL ASSERTING IT. Remark R-AFA was titled "Why Foundation is Ruled Out; AFA as Forced Replacement" - which renders as the p.7 box title AND as the running header on p.8, two of the four - opened "The choice of ZF + AFA over ZF + Foundation that it entails is nonetheless not arbitrary: it is forced by the membership structure the framework's bottom must have", and headed its fourth paragraph "AFA as the forced replacement." THE DIRECTION IS THE WHOLE FINDING. What is proved runs ONE WAY: a self-membered bottom forces the host's membership relation to be non-well-founded - quineHost_not_wellFounded, axiom-free, because requirement (Y) puts a self-loop at the bottom and a well-founded relation admits no self-loop (wf_no_selfloop). RUN BACKWARDS IT SELECTS NO THEORY. "Supplies exactly one Quine atom" is a shared INTERFACE with three mutually exclusive IMPLEMENTATIONS, measured at the primary source on disk and read as PAGE IMAGES rather than as its OCR text layer: Corollary 4.28, printed p.55, "AFA, FAFA and SAFA are pairwise incompatible axioms", and Appendix A, printed p.108, "AFA, SAFA or FAFA where there is exactly one such set". So Foundation-freeness is FORCED and AFA is CHOSEN, and the premise asserted the converse of what the corpus proves - while the sentence two clauses below, added by this same change, said the opposite in terms ("What is forced is the non-well-founded metatheory, not the particular axiom"). A false premise carrying a conclusion is this project's definition of BEDROCK, and the conclusion it carried is the narrow Forced Metatheoretic Commitment on p.9. THE CORPUS HAD ALREADY RETIRED THE CLAIM AND NAMED THIS REMARK: CLAIMS.md:119 - "no longer 'AFA is forced'", and "(The older 'why AFA specifically' argument is ZP-E Remark R-AFA; this requirements framing supersedes it.)" - and ZeroParadox/Settheory/QuineHost.lean:57, "This shrinks the old 'AFA is forced' Forced Metatheoretic Commitment to 'these requirements are the right ones'", corroborated at README.md:134 and BOTTOMELEMENT.md:28. Forcedness survived here because the change that corrected the paragraph left the title, the running header, the opening premise and the paragraph heading standing - R-LOOPCAP's measured pattern, each round writing the next round's defect. DC-24: a gate names one site and the claim lives at several. ⚠ THE SITE COUNT IS FOUR, NOT FIVE, AND THE CORRECTION IS RECORDED RATHER THAN SILENT (editorial round 2, F22): an earlier draft of this entry said FIVE rendered sites and "the two running headers". Re-derived at the DEPOSITED v3.43 artifact rather than at a build - 18 pages, extracted with pypdf and with pdfplumber, both returning "AFA as Forced Replacement" TWICE, p.7 box title and p.8 running header, because the old remark ended on p.8 ("Remark R-AFA" totals 4 renders in that PDF against 5 in the current build). So the title string rendered twice, the opening premise once and the paragraph heading once: four rendered sites from three source strings. The figure of five described an uncommitted mid-arc build rather than the artifact, which is the axis a rendered-site count goes stale on. (2) R-TWOPOLE RETURNED MISSING CHART, AND A BARE DELETION WAS THE WRONG MOVE. Striking "forced" writes the opposite one-chart sentence, "AFA is arbitrary", which is FALSE - Foundation-freeness genuinely IS forced. The fix PRESERVES forcedness where it is true, the metatheory, and removes it only where it is false, the particular axiom, at each of the three source strings. The title is now "Remark R-AFA - Why Foundation is Ruled Out; Non-Well-Foundedness Forced, AFA Adopted": the formal handle R-AFA is unchanged per R-NAMING and only the descriptive half moves, and both charts sit in it, the exclusion forced and the replacement adopted. The opening premise now separates the two halves in terms - the membership structure "forces a non-well-founded host, which is what rules ZF + Foundation out", and "which non-well-founded axiom to adopt is a further step that the forcing does not take", closing on ZF + AFA as "the canonical theory meeting the requirements, not the one theory the bottom selects". The paragraph heading is now "Non-well-foundedness is forced; AFA is the canonical replacement", which carries both charts in one line. (3) F5, SAME PARAGRAPH, AND IT IS THE SENTENCE'S SECOND REVISION, SO R-REVALIDATE WAS RUN RATHER THAN A THIRD ADJECTIVE. The first pass of this change replaced the extremum ("AFA is the minimal such theory that supplies exactly one of them") with "AFA is the canonical such theory supplying exactly one of them" - changing only the ADJECTIVE and leaving standing the DEFINITE ARTICLE that its own diagnosis had named as the failure point, ranging over a set the next sentence says has three members. The claim, stated in one line without its framing: AFA is singled out among non-well-founded set theories by supplying exactly one Quine atom. WHAT THE MEASUREMENT SHOWED, which is what this entry records rather than a re-wording: Appendix A p.108 gives that property to all three of AFA, SAFA and FAFA, so the claim is FALSE and no adjective repairs it. The singling-out is therefore DELETED, not re-worded, and what replaces it is the true sentence - "Supplying exactly one therefore does not single AFA out, so AFA is adopted as the canonical witness rather than selected by the membership structure." R-ADJACENT: the correct statement already stood two clauses away and is not paraphrased into a second copy. ⚠ AND THE FIRST PASS WROTE A SECOND CONJUNCT THAT IS ALSO DELETED NOW (editorial round 2, F11): it read "and none of the three is least among them", which PRESUPPOSES an order over the three theories that the same sentence's own citation DENIES - Corollary 4.28 makes AFA, FAFA and SAFA pairwise INCOMPATIBLE, and pairwise incompatible theories stand in no implication order, so "least among them" is not false but UNDEFINED on that set. It also did work the first conjunct had already done. R-TWOPOLE returns neither chart, since "one of the three IS least" is not true either, so the answer is deletion and not a third adjective; and the pairwise incompatibility stays stated, in the clause immediately before it, so nothing true is lost. (4) F6, SAME PARAGRAPH, AN UNSCOPED SUPERLATIVE. "Quine atoms (x = {x}) are the minimal non-well-founded objects" was stated unrestricted over all non-well-founded objects, while the warrant this remark actually carries is a minimum over CANDIDATE BOTTOMS - "the minimal option consistent with A4's additive-identity role" - three paragraphs below. No indexed declaration in ZeroParadox/BottomCannotBe.lean carries the wide form; that file was read whole, 389 lines. The first pass of this change ADDED A SCOPE instead of deleting, writing "among the candidate bottoms A4 admits, a Quine atom (x = {x}) is the minimal one, for the reason given under What remains below". ⚠⚠ THAT WAS THE THIRD FORMULATION OF ONE PROPOSITION AND IT IS NOW DELETED OUTRIGHT (editorial round 2, B3, BEDROCK, created by this change's own fix). R-REVALIDATE fired at the third revision, so what is recorded here is a MEASUREMENT and not a fourth wording. The claim, in one line without its framing: a Quine atom is the minimal bottom that A4 admits. WHAT THE MEASUREMENT SHOWED - the domain is degenerate in BOTH readings, so the sentence has no truth conditions as written. A4 is bot_join, "for every x, join bot x = x", ZeroParadox/Order/Lattice.lean:55, commented "A4: Additive identity". Read inside a lattice, bot_unique (ZeroParadox/Settheory/SetTheoryAFA.lean:142, "At most one element satisfies the join-identity - pure semilattice algebra") proves the occupant of that role is UNIQUE, so "the candidate bottoms A4 admits" is a SINGLETON and a minimum over one thing asserts nothing. Read set-theoretically instead, A4 is an equation about join and constrains membership structure NOT AT ALL, so it excludes no candidate and the restriction comes entirely from the desiderata stated three paragraphs below. Two further defects rode on it: it contradicted this remark's own opening sentence ("it is not derived from A1-A4") by attributing a selection among membership shapes TO A4; and it sat inside the scope of "That much is forced" while its own pointer target calls the same thing a COMMITMENT and not a theorem, importing a declared non-theorem into the forcedness partition, which is the one distinction this arc exists to draw. It was also a non-sequitur where it stood: circularity alone yields "so bottom can live only in a non-well-founded metatheory", and the "so" read minimality as a premise of that implication. R-TWOPOLE returns NEITHER CHART - "a Quine atom is NOT the minimal candidate bottom" is not true either - which is what makes deletion correct rather than a one-chart flip. The sentence now reads "The membership structure of ⊥ = {⊥} is circular (⊥ ∈ ⊥ ∈ ⊥ ∈ …), so ⊥ can live only in a non-well-founded metatheory. That much is forced; the particular axiom is not." - which is exactly quineHost_not_wellFounded's content, axiom-free. R-ADJACENT: the minimal-option point already stands once, in What remains, in the honest modality (a commitment), and is NOT re-copied above it in a stronger one. (5) A SIXTH FORCEDNESS SITE THAT NO FINDING NAMED, FOUND BY SWEEPING THE PROPOSITION RATHER THAN THE WORD. The machine-checked paragraph closed "So the AFA choice is not merely argued: the forcing and the realizability are settled results", which says of the CHOICE OF AFA what is true only of the REDUCTION TO REQUIREMENTS - B1's converse again, one paragraph away from B1. It now reads "So the reduction to requirements is not merely argued: the forcing and the realizability are settled results. What stays argued is which requirements to demand, below." (6) F2, RENDERED, FOUR OCCURRENCES, AND IT MISNAMED AN AXIOM. The Boffa paragraph called Boffa's weak axiom BAI, Latin capital I; Aczel's axiom is BA1, digit one. VERIFIED AT PAGE IMAGES, which is where the previous pass went wrong - it verified against the OCR text layer, which renders the subscript digit as a letter: printed p.57 (PDF 77) reads "Let BA1 be the following axiom: Every extensional graph is isomorphic to Vza for some transitive set a", with Proposition 5.1 on the same page, "Assuming BA1 the reflexive sets form a proper class"; Exercise 5.14 on printed p.65 (PDF 85) defines BA2, which fixes the sibling as a digit; and Exercise 5.10 on printed p.62 (PDF 82) reads "Show that BA 1 does not imply sigma". A wrong identifier fails SILENT - BAI is not in Aczel's Index of Named Axioms, so a reader who checks finds nothing. DC-41's shape with a new cause. The name is written with a subscript tag, BA&lt;sub&gt;1&lt;/sub&gt;, matching Aczel's printed BA-sub-1 and PDF_Rendering_Standards.md section 5, which forbids Unicode subscript characters and requires the tag. ⚠⚠ AN EARLIER DRAFT OF THIS ENTRY WROTE IT FLAT AND GAVE A REASON THAT IS FALSE ABOUT OUR OWN TOOLING (editorial round 2, F18, DC-53, whose rule is RUN IT FIRST). That reason said a sub-tagged numeral sits at a different baseline and "pdfplumber's extract_text drops it, which would leave the corrected name invisible to the very claim sweep that caught the wrong one". THE CLAIM SWEEP IS check_paths.py AND IT DOES NOT USE pdfplumber: tools/verify/check_paths.py:1372-1381 defines _pdf_text with "from pypdf import PdfReader", falling back to PyPDF2, and joins pg.extract_text() over the pages. RUN HERE, BOTH EXTRACTORS OVER THIS DOCUMENT'S OWN RENDER: pypdf reads every sub-tagged numeral in it as contiguous text - c&lt;sub&gt;0&lt;/sub&gt; 18 hits, c&lt;sub&gt;1&lt;/sub&gt; 44, P&lt;sub&gt;0&lt;/sub&gt; 23, S&lt;sub&gt;0&lt;/sub&gt; 5 - while pdfplumber returns 0, 5, 0 and 0 for the same four, because it relocates the shifted glyph rather than keeping the string contiguous. So the "0 hits with the tag / 4 without" measurement was a true number of the WRONG OBJECT: the object it was taken on is not the sweeper. The tag is therefore restored, the flat form is gone, and the residual limit is stated rather than hidden - a sub-tagged name is visible to check_paths.py and is NOT visible to a pdfplumber-based probe, so any future sweep for this name must use the sweeper or search for the stem BA alone. (7) F3, RENDERED, THE RELATIVE CLAUSE HUNG ON THE WRONG LOCATOR. "(Aczel 1988, Exercise 5.14(i), where it is introduced as Boffa's strengthening of BAI)" put two facts on one locator. Exercise 5.14, printed p.65, contains the definition of BA2 and then "Show that (i) BAFA <=> BA1 + BA2. (ii) FAFA2 => BA2" - the equivalence half is exactly right and nothing else is there. The phrase "Boffa's strengthening of BA1" is printed p.59, six pages earlier, on the page where BAFA is formulated ("Every exact decoration of a transitive subgraph of an extensional graph can be extended to an exact decoration of the whole graph") and where Aczel's own Index of Named Axioms places BAFA. The citation is now split so that each locator carries what it actually says. Both pages read as images. (8) F4, RENDERED, AN ATTRIBUTION ACZEL DOES NOT MAKE. The previous pass MOVED "(Boffa 1968)" from BAFA onto BA1, which is an act of attribution rather than the preservation of an inherited one, and Aczel attaches no year to BA1 anywhere. His References, printed pp.123-124, read as images, carry THREE 1968 entries - Boffa 1968a, "Graphes extensionelles et axiome d'universitalite", Zeitschrift fur math. Logik und Grundlagen der Math. 14:329-334; Boffa 1968b, "Les ensembles extraordinaire", Bull. Soc. Math. Belg. 20:3-15; and Boffa & Beni 1968 - and the only year-bearing Boffa citation in chapter 5 is "(See Boffa 1972a)" at Exercise 5.10, attached to BAFA and not to BA1. The bare year is therefore DROPPED and no finer one invented: Proposition 5.1 carries the proposition, and the prose attributes both axioms to Boffa by name, so nothing about authorship is lost. ⚠ Boffa 1968a, 1968b and Boffa & Beni 1968 were NOT retrieved - rung 1 only - and this rests on what ACZEL does and does not say, not on those papers. ⚠⚠ AND A SECOND CITATION WENT OUT IN THE SAME PARENTHESIS, WHICH THIS ENUMERATION DID NOT ENUMERATE (editorial round 2, F16, DC-24's shape). The deleted parenthesis read "(Boffa 1968; the AFA/Boffa comparison in Barwise & Moss, Vicious Circles, CSLI 1996)", and dropping the bare year took the Barwise & Moss pointer with it while this item explained only the year. Measured at the deposited v3.43 PDF: "Barwise" and "Vicious Circles" each occur once, on p.8, and both are 0 in the current render. It is an IMPROVEMENT rather than a loss - a rung-3 secondary comparison is replaced by rung-4 primary locators read at page images, Exercise 5.14(i) for the equivalence, printed p.59 for the strengthening and Proposition 5.1 for the proper class - and no claim in the paragraph loses support. The corpus keeps the secondary source: ZeroParadox/Settheory/QuineHost.lean:88-89 still carries it, so only this document's rendered text drops it. The defect was that an enumerating changelog did not enumerate the deletion, not the deletion. (9) TWO GRAMMATICAL FENCES IN THE SAME PARAGRAPH, the same definite-article failure this arc exists to fix. "The permissiveness is therefore inherited from the weaker axiom" is correct for its antecedent, the proper class of reflexive sets reached from BA1 via Proposition 5.1, and FALSE as a claim about BAFA's permissiveness in general, since Exercise 5.10 shows BAFA implies sigma while BA1 does not; it now reads "That permissiveness". And "This development formalizes no part of Boffa's axiom" became ambiguous the moment the paragraph named TWO Boffa axioms; it now reads "no part of either Boffa axiom". (10) B2, BEDROCK, THE RETRACTED PROPOSITION LIVE ON RENDERED p.3 OF THIS SAME PDF, SIX PAGES FROM THE REMARK THAT NOW SAYS THE OPPOSITE - AND THE ELEVEN-PHRASING SWEEP ABOVE COULD NOT REACH IT (editorial round 2; DC-62, occurrence 8 in that row). The DA-1 Path 1 block read "AFA (ZF + AFA) is the consistent set-theoretic home for this structure - chosen because the framework requires it, not the reverse", which carries BOTH halves of what B1 retracted, in one sentence. UNIQUENESS: "the consistent set-theoretic home" - consistent is a MATHEMATICAL predicate here, not a conventional one, and there is no hedge, while Corollary 4.28 (printed p.55) makes AFA, FAFA and SAFA pairwise incompatible and Appendix A (printed p.108) gives each of the three exactly one reflexive set, so all three are consistent homes for this structure and the definite article is false. FORCEDNESS: "chosen because the framework requires it", whose "it" is AFA - exactly the proposition CLAIMS.md:119 records as retired, and the converse of quineHost_not_wellFounded, which runs one way only and backwards selects no theory. WHY THE SWEEP MISSED IT, WHICH IS THE ROW'S OWN LESSON: all eleven phrasings were keyed to strings at sites ALREADY FOUND, and this site's vocabulary is home and requires, matching none of them. DC-62's detector is to state the PROPERTY using no string from any found site - "exactly one host theory can accommodate the framework's least element" - and probing THAT, by vocabulary (home, host, theory, metatheory behind a definite article), by polarity (no other, nothing else, no alternative) and by part of speech (requires, demands, needs it), is what reached p.3. R-TWOPOLE returned MISSING CHART, so the fix ADDS the plurality and does NOT flip to "AFA is arbitrary", which is false. ⭐ THE REPLACEMENT IS ADOPTED, NOT DRAFTED (R-ADJACENT), AND THAT IS THE WHOLE POINT OF THIS SITE: README.md:134 and CLAIMS.md:117 already carry the migrated register, and CLAIMS.md:119 names THIS REMARK as the superseded surface ("The older 'why AFA specifically' argument is ZP-E Remark R-AFA; this requirements framing supersedes it"), so what was needed here was a completed migration and not a new framing. It now reads "AFA (ZF + AFA) is a consistent set-theoretic home for this structure, and the commitment is not the adoption of AFA specifically: it is a set of requirements on the host theory - that the bottom is a self-containing Quine atom (⊥ = {⊥}), and that this atom is unique - of which AFA is the canonical example." - README.md:134's sentence, with only the true half of the indicted one ("a consistent set-theoretic home for this structure") retained, since striking the whole sentence would lose the fact that ZP-J T-EXEC's role result has a set-theoretic home at all. ⚠ TWO DRAFTED VERSIONS WERE DISCARDED BEFORE THAT: the first closed on "- Remark R-AFA separates the two", which made the paragraph point at the remark TWICE three sentences apart while the pointer already stood at its end (caught by the rendered count going 5 to 6); the second paraphrased README.md:134 as "adopted as the canonical theory meeting the requirements" instead of quoting it. Rounds 1 and 2 each drafted fresh prose at this site's siblings and each wrote the next round's defect; the canonical wording was available to both. The other two definite-article host phrasings in this document were read and left standing: p.7's "the canonical theory meeting the requirements, not the one theory the bottom selects" fences the mathematical reading in the same breath, and p.8's "the host's distinguished bottom" is about a bottom, not a theory. (11) B4, BEDROCK, A def OVER A TRIVIALLY-INHABITED HYPOTHESIS PRESENTED AS PROVED ABOUT A SET THEORY, UNDER THE HEADING "What is machine-checked" (editorial round 2). The realizability clause closed "and AFA is the canonical example (afaStructure_isQuineHost)", inside the list introduced by "Proved there:". VERIFIED AT THE LEAN, NOT AT THE DOCSTRING ABOUT IT: afaStructure_isQuineHost is a @[reducible] def and not a theorem (ZeroParadox/Settheory/QuineHost.lean:178-185); it takes [ZPSemilattice L] [AFAStructure L], the LATTICE-level class rather than a set theory; and AFAStructure is trivially inhabited on every ZP-A lattice by instance toAFAStructure (ZeroParadox/Computability/SelfApp.lean:131). ZeroParadox/Settheory/SetTheoryAFA.lean:63-72's NO-GO gauge forbids the inference in terms - "[AFAStructure L] imports no anti-foundation content", "universal inhabitation is no evidence for a universality claim about AFA, the construction being definitional", "⚠ There is no non-member" - and R-GATED says a requirements class is informative only if something FAILS to be a member. R-TWOPOLE returned MISSING CHART and there is a TRUE weaker reading the fix must keep, that the framework's own lattice-level ENCODING of AFA meets the requirements, which is what the def exhibits; so the fix ADDS THE SCOPE rather than striking the sentence, and it does so by MOVING the clause out of the "Proved there:" list into its own sentence: "AFA is the canonical example, exhibited off the framework's own AFAStructure (afaStructure_isQuineHost) - a definition rather than a theorem about the set theory, and one every ZP-A lattice supplies trivially (the NO-GO gauge in ZeroParadox/Settheory/SetTheoryAFA.lean)." ⭐ THE SCOPE PHRASE IS ADOPTED, NOT DRAFTED: "the canonical example, exhibited off the framework's own AFAStructure" is CLAIMS.md:119's and ZeroParadox/Settheory/QuineHost.lean:48-49's own wording, which already names the witness's true scope. Only the def-versus-theorem fence is DRAFTED, and adoption was not possible there because that is precisely the point the two Lean files disagree on, so no migrated surface states it. R-ADJACENT also holds for the trivial-inhabitation half: p.9 of this same PDF already says "every ZP-A lattice supplies AFAStructure trivially". A first draft read "AFA enters as the intended example rather than as a further theorem", which invented a register where CLAIMS.md had one; it is discarded. ⛔ TWO LEAN FILES DISAGREE WITH EACH OTHER AND THAT IS NOT FIXED HERE: QuineHost.lean:48 and :53-56 list "AFA satisfies (X), (Y), (Z)" under "What is proved", which is what the gauge says may not be inferred. The conflict is upstream, is corpus, and is Tim's ruling (DEFECTS.md AFAPROVED-1). This wording is accurate whichever way that ruling goes, because it asserts only what the def IS and what the gauge SAYS, and it credits AFA with nothing the kernel did not check. README.md:134 carries the same framing, is downstream of the same ruling, and is untouched. (12) F10, THE REMARK CONTRADICTED ITSELF ON ITS OWN CENTRAL COUNT, AND THIS SCRIPT WAS THE LONE OUTLIER AGAIN (editorial round 2). p.8 read "reduced to three requirements a host must supply - Foundation-freeness, a Quine atom, and its uniqueness", against p.9 of the same remark ("the right two requirements to demand") and against the very next clause of its own sentence, which calls Foundation-freeness FORCED and therefore not supplied. QuineHost.lean:33 carries the identical phrase with the other number, "the two requirements a host theory must supply", and :38 states why: "A third requirement, (X) Foundation-free, is NOT assumed: it is forced by (Y) and proved here." The class has exactly two propositional fields, bot_selfMem and selfMem_unique. Every other surface says two - QuineHost.lean:33, README.md:134, BOTTOMELEMENT.md:28, scripts/build_dictionary_map.py:678. ⭐ THE COUNT AND ITS WORDING ARE BOTH ADOPTED, NOT DRAFTED: it now reads "reduced to the two requirements a host theory must supply - (Y) a Quine atom ⊥ = {⊥} and (Z) its uniqueness", which is CLAIMS.md:119's and QuineHost.lean:33's sentence including the (Y)/(Z) labels the class itself uses; and the Proved-there list opens "the third property, (X) Foundation-freeness, is not assumed - it is forced by (Y)", which is CLAIMS.md:119 verbatim in substance and QuineHost.lean:38's "A third requirement, (X) Foundation-free, is NOT assumed: it is forced by (Y)". A first draft wrote "not a third requirement but a consequence, forced for any such host" - a paraphrase of a sentence that already existed twice; it is discarded. (13) FIVE PRECISION FIXES IN THE SAME REMARK, EACH VERIFIED AT ITS OWN ARTIFACT (editorial round 2, F12-F15 and F17). F14, ANTECEDENT DRIFT: the paragraph heading "The framework's readings of ⊥ corroborate this (they do not prove it)" resolved "this" to the preceding paragraph's Foundation exclusion, which that paragraph has just called MACHINE-CHECKED (no_quine_atom / no_membership_cycle, ZeroParadox/Settheory/Wall.lean, both in section PurityCheck) - and a theorem needs no corroborating. The paragraph's own closing clause names the real referent, the PREMISE that ⊥ is circular. It now reads "The framework's readings of ⊥ support the premise that ⊥ is circular; the exclusion itself is a theorem." F15: the trailing clause "formalized later in the ZP-J AFA layer" is DROPPED. RUN, QuineHost across scripts/: build_zpa.py 3, build_zpe.py 8 before this change, build_dictionary_map.py 1, build_zpj.py 1, and build_zpj_afa_addendum.py 0. The full repository path already locates the development, so the clause added only an ambiguity about whether "the ZP-J AFA layer" names the Lean development or the addendum document. F12: "the surviving clause is vacuous as a pinning condition" now reads "uninformative", which is R-GATED's own register for a condition every element satisfies. ⚠⚠ AND THE COLLISION IS INSIDE THE LEAN, NOT ONLY HERE, WHICH IS WHY THE WORD IS AVOIDED RATHER THAN RE-ASSIGNED - the finding's premise that this document was the outlier is HALF WRONG, measured at the files: QuineHost.lean:51 uses "non-vacuous" for SATISFIABLE (a concrete model exists) and this file's own v3.43 entry uses "VACUOUSLY" for satisfied-because-there-are-no-witnesses, both the logician's sense; while ZeroParadox/Settheory/RequirementsGap.lean:107-112 uses it for exactly the sense the rendered sentence needed - "Every element is a fixed point, so every object is a witness and the requirement is vacuous - no instance is pinnable." One word, two opposite technical senses, both inside the corpus. RECORDED, NOT RESOLVED: which sense is house is a corpus question and not this document's to settle, and "uninformative" is true under both, so the rendered text is accurate whichever way that goes. F13: the t_exec qualifier is RESTORED on p.9. Its docstring (ZeroParadox/Settheory/SetTheoryAFA.lean, section II) reads "No bridge axiom: the field bot_self_mem is the input, and quine_unique is not used"; p.3 of this same PDF carried "(axiom-free, given the field bot_self_mem)" and p.9 had dropped it, DC-28 inside one document. The declaration, the path and the axiom-free claim were all correct; only the qualifier was missing. F17: "the two halves" named two DIFFERENT pairs in one remark - on p.7 the forced/adopted split, on p.8 the cited-fact/checked-mechanism split. The Boffa heading now reads "the cited half and the checked half are separate", so the phrase has one referent. ⛔ WHAT THIS CHANGE DOES NOT TOUCH: Foundation's exclusion and its footprints; the counter-model half of the Boffa paragraph with its one-direction fence, whose vocabulary moved but whose content did not; and the Forced Metatheoretic Commitment paragraph's substance, including its named falsifier, where only the t_exec qualifier was restored. No claim gains support, and every edit in items (10) to (13) either DELETES a claim, weakens one to what was measured, or corrects a count. ⚠⚠ THE PROPOSITION WAS SWEPT, NOT THE WORD, WHICH IS THE MEASURED LESSON OF THIS ARC: the previous sweep ran five phrasings and all five targeted MINIMALITY while the proposition actually retracted was FORCEDNESS, which is exactly how B1 survived it. Run here: check_paths.py --full --claim over 473 surfaces including 40 rendered PDFs, eleven phrasings varied by AXIS - "forced replacement", "not arbitrary", "the canonical such theory", "minimal non-well-founded", "the AFA choice" and "BAI" (the DELETED strings), "AFA is forced" (the claim's noun alone, with no deleted string in it), "AFA specifically" (POLARITY, how the corpus states the retirement), "forced metatheoretic replacement" (VOCABULARY), and "minimal such theory" and "supplies exactly one" (PART OF SPEECH, and the bare predicate) - 37 sites across 15 files, every hit read. In this document's rendered text every deleted string now returns zero, and so does "Boffa 1968". ⚠⚠ TWO SURVIVING HITS ARE NAMED RATHER THAN SWEPT, AND THE FIRST IS THE SAME BEDROCK PROPOSITION LIVE IN A SECOND DEPOSITED PDF: ZP-A_Lattice_Algebra.pdf, from scripts/build_zpa.py:164, reads "Foundation excludes the Quine atom; AFA uniquely permits it. AFA is the forced metatheoretic replacement" - and both the forcedness and the UNIQUELY are contradicted by Corollary 4.28 and Appendix A p.108 as measured above. It is outside this document, owes its own version bump, companion review and gate round, and is recorded rather than touched here. ZP-J_Keystone_Addendum.pdf carries "the minimal non-well-founded coalgebra", which is a different and already-scoped claim about coalgebras, not F6's shape. And this file's own v3.2 entry below records that v3.2 identified AFA "as the forced metatheoretic replacement": that entry describes an EDIT, which is immutable (DC-60), and it stands as the record of what v3.2 did. ⚠ EVERY COUNT HERE IS RE-DERIVED FROM THE TOOL'S OWN OUTPUT AT THE MOMENT OF WRITING, and none is carried from the previous pass. "Boffa 1968": 11 sites across 5 files, of which FIVE are the same-grain bare-year sites outside this document - BOTTOMELEMENT.md:28, CLAIMS.md:119, ZeroParadox/Settheory/QuineHost.lean:45 and :88, and scripts/build_dictionary_map.py:678 - and none of the five is in a rendered PDF now that this one is fixed. "canonical example": 10 sites across 5 files. "minimality": 78 sites across 36 files. The earlier draft of this entry gave the first of those as two sites and the second as seven, and stated a union over five phrasings as a single figure of 89 across 41 without saying it was a union; none of those figures is carried. That draft also called ZeroParadox/Settheory/QuineHost.lean 213 lines. It is 212 - 10,684 bytes, 212 LF bytes, last byte 0x0A, measured here - and 213 is the element count of a naive split on the newline, whose final element is the empty string after the trailing newline. Every other locator in that draft verifies exactly: the Expected-footprint docstring at 189-200, its boffa_fails_unique expectation line at 194, section PurityCheck at 202-212, and #print axioms boffa_fails_unique at 207. ⚠ NO COMPANION CHANGE, AND IT IS MEASURED ON THE AXIS THE PREVIOUS CHECKS DID NOT RUN: earlier passes searched build_zpe_companion.py for Vicious, Barwise, Boffa, anti-foundation, QuineHost, Aczel, host theory, unique and reflexive, none of which would have caught "forced". Searched here: "forced" and "force" 4 hits, "AFA" 2, "Foundation" 1, "canonical" 1, and zero each for "arbitrary", "non-well-founded", "replacement" and "host". Every hit outside the companion's own changelog is DA-1 Path-1 material or the CC-2 label - "Path 1 (AFA self-containment)" at line 336, "CC-2 (bottom = {bottom}, a ZP-A Forced Metatheoretic Commitment)" at line 369, and "foundational assumption" at line 286 - and none of them asserts that AFA specifically is forced. The companion therefore carries no part of Remark R-AFA, is not materially stale, and its version is unchanged at v1.19.
v3.43: PA-2 - A CITED LITERATURE FACT STATED IN A MACHINE-CHECKED SLOT, AND CREDITED TO A TOY-MODEL THEOREM (DEFECTS.md PRIOR-ART-DB-ORDINARY, finding PA-2; prior_art gate 2026-09-15). Remark R-AFA's "What is machine-checked (the requirements framework)" block read "Boffa's anti-foundation axiom is excluded as too permissive, admitting a proper class of atoms rather than one (boffa_fails_unique)", in the same grammatical slot as Foundation's exclusion and citing boffa_fails_unique for the whole of it. TWO DIFFERENT PROPOSITIONS WERE FUSED. That Boffa's axiom admits a proper class of Quine atoms rather than one is a CITED fact (Boffa 1968); this corpus formalizes no part of Boffa's axiom. What boffa_fails_unique proves, verified at ZeroParadox/Settheory/QuineHost.lean lines 132-147, is the MECHANISM over a two-element carrier where BoffaMem holds of every pair: no element is THE self-membered one, footprint axiom-free (Bool.noConfusion), the measurement EMITTED by #print axioms boffa_fails_unique inside section PurityCheck, ZeroParadox/Settheory/QuineHost.lean lines 202-212. It mentions neither Boffa's axiom nor any set theory. The Boffa clause is therefore lifted out of the machine-checked list into its own sub-paragraph, which separates the cited half from the checked half and STATES THE DIRECTION: the toy model is a counter-model separating requirement (Y), that the bottom is a Quine atom, from requirement (Z), that the atom is unique - so uniqueness does not follow from self-membership. ⚠ THE REVERSE DIRECTION IS TRUE BUT IS NOT CARRIED BY A THEOREM HERE, AND THOSE ARE DIFFERENT FACTS: that requirement (Z) alone yields no Quine atom holds mathematically - selfMem_unique, "for every x, mem x x implies x = bot", is satisfied VACUOUSLY by any carrier in which nothing is self-membered, so (Z) cannot deliver (Y) - but no corpus declaration stating it was located as of 2026-09-26, searched as follows: check_paths.py --claim --full over 473 tracked surfaces, 40 of them rendered PDFs, in three phrasings varied by AXIS - "uniqueness alone" (VOCABULARY), "nothing is self-membered" (POLARITY, how the corpus would state the vacuous-satisfaction side) and "uniqueness does not force" (PART OF SPEECH, finite verb for the nominal), zero hits each; plus an identifier sweep on selfMem_unique over every tracked .lean, .md and .py, returning only the class field, its two instances, quineHost_selfMem_iff, and two prose pointers - no counter-model in that direction. The rendered text states the checked direction only ("it blocks one direction only") and this fence stays out of the PDF. ⛔ FOUNDATION'S EXCLUSION IS UNTOUCHED: zfSet_no_quine_bottom IS in-kernel about Mathlib's real ZFSet, so that half of the list was accurate and is left verbatim. The closing sentence ("the forcing and the realizability are settled results") is unchanged and does not cover Boffa. ⭐ R-ADJACENT - THE WORDING IS ADOPTED, NOT INVENTED: the accurate fence already stood in six places and ZP-E was the single copy that dropped it; the register here is adapted from README.md's Framework-commitments paragraph, the closest of the six to PDF prose, against QuineHost.lean's canonical form as the authority. ⛔ R-TWOPOLE returned a MISSING CHART, not INVARIANT, and the fix ADDS it: the deleted sentence's one-face framing was exclusionary ("Boffa is ruled out"), and the other chart holds too - dropping (Z) makes a host theory no less consistent, it makes the requirement VACUOUS, with nothing pinned. That half is now stated, grounded in what boffa_fails_unique itself exhibits. Its order-theoretic image (the identity operator's fork flung fully open, ZeroParadox/Settheory/RequirementsGap.lean) is a shared SHAPE across settings and is deliberately NOT cited here as a witness. ⚠ THE DELETED WORDING WAS SWEPT, NOT THE NEW: check_paths.py --full --claim over 473 files, 40 of them rendered PDFs, in four phrasings varied by AXIS - "excluded as too permissive" (the deleted string), "too permissive" (VOCABULARY), "admitting a proper class" (PART OF SPEECH, gerund for finite verb), "proper class of atoms" (the bare NOUN PHRASE, which drops the exclusion polarity and would catch a site stating the literature fact approvingly). Not located outside this file's own changelog as of 2026-09-26, searched as stated. ⭐ THE SIXTH OF THOSE SITES IS THIS TICKET'S DC-28 SHAPE AGAIN: fmc_guide.md keeps "too permissive" in its general-reader squeeze (too strict / too permissive / exactly one) and then fences it correctly one paragraph below - Boffa's rule "fails for a reason long known in the literature", with "a small model makes that concrete (boffa_fails_unique) rather than deriving it in-kernel about that theory". Left untouched: it is already right, and the squeeze wording is the guide's own register. No companion change: build_zpe_companion.py returns zero hits for Boffa, anti-foundation, unique/uniqueness, host theory and QuineHost, so it carries no part of the fused claim, is not materially stale, and its version is unchanged at v1.19.
v3.42: GENTZEN-5 - TWO SCHEMAS IDENTIFIED WITHOUT THE BRIDGE THAT IDENTIFIES THEM, IN TWO DEPOSITED PDFs (DEFECTS.md GENTZEN-5; editorial E4-5 and prior_art PA6-1, found independently, 2026-09-23). Remark R-eps0's parallel-structures sentence read "the minimum ordinal whose well-ordering PA cannot prove", while the same remark earlier read "transfinite induction at every ordinal strictly below ε₀". THOSE ARE TWO DIFFERENT SCHEMAS - transfinite induction along an ordering is an INDUCTION schema, and the well-ordering of an ordering is the statement that it is WELL-FOUNDED - and they are identified only through an ordinal NOTATION SYSTEM, which no surface here stated. ⚠ THE BRIDGE WAS NOT LOCATED AS OF 2026-09-23, SEARCHED AS FOLLOWS: check_paths.py --claim --full over every tracked surface and all 40 deposited PDFs, phrasings varied by VOCABULARY - "notation system", "PRWO" - with no hit in any ZP-E or ZP-L rendered text. This change replaced the VOCABULARY at that sentence, and at its twin in the companion (comp v1.19), with the transfinite-induction form "the minimum ordinal up to which PA cannot prove transfinite induction". It was chosen because it needs no notation caveat; because it agrees with CLAIMS.md's Gentzen row as that row stood here, and with the canonical definition of a proof-theoretic ordinal (the supremum of the ordinals for which the system proves transfinite induction); and because it read correctly into both continuations - the ZP half of the parallel here, Goodstein's theorem in the companion. ⛔ THE CHART WAS NOT TOUCHED, AND THAT WAS NOT A JUDGEMENT CALL: adversary and prior_art both ruled the FROM-ABOVE chart right at this site in round 1, the other half of the parallel ("ZP locates the minimum state displacement at which no external program can hold ⊥ as a static string") being itself a least-at-which-something-fails shape; and the from-below sufficiency direction stood verbatim two paragraphs above with its 1936 credit and was left there. R-TWOPOLE returned INVARIANT, the ratified null case: this moved VOCABULARY inside a settled chart and reversed no direction, so no second chart was owed. ⭐ AND THE SWAP MOVED THE CLAIM ONTO SOURCED GROUND. The well-ordering form needed, for its MINIMUM, that PA proves the well-ordering of every ordinal below ε₀ - one step a gate DERIVED, never a passage anyone read. The transfinite-induction form needs the below-ε₀ PROVABILITY of transfinite induction, which Gentzen reports as already known (bekanntlich) crediting Hilbert-Bernays at Math. Annalen 119 (1943) p.140 footnote 3, read here as page images and filed, and which this remark already carried two paragraphs above with that credit. What is sourced on the well-ordering side is Rathjen arXiv:1405.4484v1 Thm 2.8(ii), read at a page image and filed: assuming PA is consistent, PA does not prove PRWO(ε₀). ⚠ ALSO IN THIS CHANGE, NON-RENDERING: the v3.41 entry below glossed its own new wording as "the least α at which PA fails to prove transfinite induction" - that gloss IS the unstated bridge, asserted as fact one line from the edit that introduced it, and it is dropped; the v3.41 and v3.40 entries are past-tensed where they described the companion's wording in the present tense, their quotations kept intact (DC-60: a changelog describes the EDIT, which is immutable, not the ARTIFACT, which moves). This change added no claim about what PA cannot prove at ordinals ABOVE ε₀, made no claim about what Gentzen's § 2 proves, never wrote "Hilbert-Bernays' theorem", cited the 1938 Neue Fassung nowhere, and cited the primary source only. Companion moves with it (comp v1.19).
v3.41: GATE ROUND 1 REMEDIATION - A MINIMUM TAKEN OVER A SET THAT IS EVERYTHING (adversary F3, 2026-09-23). Remark R-ε₀'s parallel-structures paragraph read "The proof-theoretic analysis locates the minimum ordinal strength at which PA cannot describe its own consistency from within." READ COMPOSITIONALLY THAT PICKS A MINIMUM OVER THE WHOLE ORDINAL CLASS: Gödel's second incompleteness theorem is UNCONDITIONAL, so there is no ordinal strength at which PA CAN describe its own consistency from within, and a minimum over everything singles out nothing. Worse, "the minimum ordinal strength at which PA CANNOT" implicates that BELOW ε₀ PA CAN - which contradicts this same remark three sentences earlier, where Gödel's second theorem is stated as the reason PA cannot prove Con(PA) from within at all. ⚠ THE SENTENCE IS PRE-EXISTING AND v3.40 EDITED IT, SO THIS ARC OWNS IT: v3.40 corrected the SUBJECT, which had credited Gentzen with the MINIMALITY (the necessity half, which is not his), and left the PREDICATE malformed. v3.41 set it to "The proof-theoretic analysis locates the minimum ordinal whose well-ordering PA cannot prove" - a well-formed minimum over a PROPER subclass, since every ordinal strictly below ε₀ is excluded from it - and v3.42 above replaced that VOCABULARY while keeping this chart. Its implicature, that PA CAN prove transfinite induction below ε₀, is TRUE and is stated with its credit two paragraphs above. ⛔ R-TWOPOLE, RUN BEFORE THE FIX RATHER THAN AFTER IT: BOTH charts hold of ε₀ - from below it is the least ordinal strength SUFFICIENT to prove Con(PA), from above the least ordinal up to which PA cannot prove transfinite induction - and this site takes the FROM-ABOVE one for a stated reason. The sentence is one half of an explicit parallel, and the other half ("ZP locates the minimum state displacement at which no external program can hold ⊥ as a static string") is itself a capacity-runs-out shape, so the from-below chart would break the parallel the sentence asserts. NEITHER CHART IS DELETED: the from-below sufficiency direction is stated verbatim two paragraphs above with its 1936 credit, and ZP-L carries the from-below chart under the standing per-document split. ⭐ R-ADJACENT - THE WORDING IS ADOPTED, NOT INVENTED: it is this document's own companion's existing from-above form, which v3.40 reviewed and recorded as not materially stale, so formal and companion now stand in the SAME chart rather than merely compatible ones. ⛔ THE ABOVE-ε₀ FENCE IS STILL AT ZERO: a least-element claim asserts nothing about upward closure, so no surface here states what PA cannot prove at ordinals ABOVE ε₀. Every v3.40 fence is unchanged: never "Hilbert-Bernays' theorem", no claim about what § 2 proves, never the 1938 Neue Fassung, and the primary source only. Companion REVIEWED and unchanged, for the reason just given.
v3.40: GENTZEN CREDITED WITH A BICONDITIONAL HE PROVED ONE ARROW OF, IN AN ALREADY-DEPOSITED PDF (DEFECTS.md GENTZEN-3; copy_editor panel 2026-09-22, all three readers indicting independently, one of them writing "I think F4 is likely mine alone"). Remark R-ε₀ read "Gentzen established that transfinite induction up to ε₀ is necessary and sufficient to prove Con(PA)." THE PROPOSITION IS TRUE AND THE SUBJECT IS WRONG. SUFFICIENCY IS HIS: transfinite induction up to ε₀ proves Con(PA), Math. Annalen 112 (1936) 493-565. NECESSITY - that no smaller ordinal would do - is the other direction and rests on different ground: the provability in PA of transfinite induction at every ordinal strictly below ε₀, which Gentzen reports as already known (bekanntlich) crediting Hilbert-Bernays at Math. Annalen 119 (1943) p.140 and its footnote 3, together with Gödel's second incompleteness theorem. The two halves are now attributed separately, and the Gödel sentence that used to follow is absorbed into the second half so the Gödel fact is stated once rather than twice and its pronoun no longer dangles. ⚠ ALSO FIXED, SAME REMARK AND SAME DEFECT: "Gentzen locates the minimum ordinal strength at which PA cannot describe its own consistency from within" credited him with the MINIMALITY, which is the necessity half wearing different words; the subject is now "the proof-theoretic analysis". ⛔ NEITHER ARROW IS DELETED (R-TWOPOLE): a fix that drops one direction rather than attributing both writes the opposite one-chart sentence, which is how the sibling ZP-L arc's round-1 BEDROCK defect was made. ⛔ FENCES HELD: never "Hilbert-Bernays' theorem" - nobody on this project has opened Grundlagen der Mathematik II, so what is asserted is what Gentzen WROTE on a page we have read; no claim whatever about what his § 2 proves, since pp. 145-155 are unopened here; and never the 1938 Neue Fassung, which p.140 footnote 4 identifies and which is a second consistency proof, i.e. the sufficiency half again. Verified at the primary source read as page images: .claude-local/papers/gentzen_1943_beweisbarkeit_unbeweisbarkeit_anfangsfaelle_transfinite_induktion_mathann119.pdf, p.140 (PDF page 2) for the bekanntlich sentence and footnotes 1-4. ⚠ Companion REVIEWED and unchanged: it then carried the from-above form "the proof-theoretic ordinal of Peano Arithmetic, the minimum ordinal whose well-ordering PA cannot prove", asserted no date and attributed no direction to anyone, so it was not materially stale. (comp v1.19 later replaced that vocabulary; see v3.42.)
v3.39: DA-1/KLEENE CLASS, GATE ROUND 4 SECOND PASS (Tim ruling, 2026-09-15): Remark R-DA1 said DA-1 is 'grounded in ZP-A CC-2 and R3', beside the Status block's primary formal grounding DP-2; it now says DA-1 is closed given DP-2 (da1_minimal_path), with CC-2 and R3 motivating it and ZP-C L-INF as independent corroboration.
v3.38: DA-1/KLEENE CLASS, GATE ROUND 4 (Tim rulings, 2026-09-15): T5 Selection said the least-fixed-point face makes 'every landing from epsilon-0 up fire (epsilon0_min_eq_max)'; 'landing' was undefined, and read as every ordinal from epsilon-0 up it follows from monotonicity and h-eps0 alone, so the clause now reads 'every fixed point of alpha -> omega^alpha fires (hfp_from_epsilon_zero, epsilon0_min_eq_max)'. The Path 3 conclusion 'Instantiation and execution are the same act' now reads 'Given DP-2, instantiation and execution are the same act (DA-1)'.
v3.37: DECISION BATCH REMEDIATION AFTER GATE ROUND 3, SECOND PASS (Tim ruling, 2026-09-15): the DA-1 Status block said 'Kleene fixed-point is the in-scope formal counterpart' of AIT; it now says the Kleene structure is its in-scope counterpart, carried as a KleeneStructure requirement (botCode_is_quine), not a proof of the AIT claim.
v3.36: DECISION BATCH REMEDIATION AFTER GATE ROUND 3 (Tim rulings, 2026-09-15): T5 Selection credits each face of epsilon-0 with its own direction: a monotone map sending the tower's stages to c0 and epsilon-0 to c1 sends no ordinal below epsilon-0 to c1 (supremum face, fundamentalSeq_cofinal) and sends every fixed point of alpha -> omega^alpha to c1 (least-fixed-point face, hfp_from_epsilon_zero); it had said 'Both faces of epsilon-0 carry this' of the downward direction alone. Deriving h-eps0 is open 'from the 2-adic structure'. The Open Items OQ-A1 cell names the monotone map and the tower stages beside h-eps0. DA-1 PATH 3 (pre-existing bedrock, editorial round 3 B1): the DA-1 synthesis paragraph, the DA-1 Status block, the DA-1 validation row and the endnote said Paths 1 and 3 are formally closed / IN LEAN SCOPE and that DA-1 is grounded in them or closed in Lean via ZP-K. They now carry the CLAIMS.md DA-1 row: Path 1 is witnessed by da1_closed_concrete, which proves IsQuineAtom (bottom : MachinePhase) and nothing computational; Path 3's witness is the machinePhaseKleene botCode_is_quine field, a KleeneStructure requirement, not a second independent proof; da1_paths_unified carries them as a conjunction of witnesses, and that they name one structural fact is the framework's reading; DA-1 is closed given DP-2.
v3.35: ADVERSARY GATE ROUND 3 (bedrock, D1): the T5 traceability row said 'given the alignment hypothesis h-eps0, nothing below epsilon-0 fires', dropping two of snap_unconditional's three hypotheses (monotonicity, and the tower stages sent to c0); a monotone map with h-eps0 can fire at 1. The row now names the monotone map sending the tower's stages to c0, as the T5 box already did.
v3.34: DECISION BATCH REMEDIATION AFTER GATE ROUND 2, SECOND PASS (Tim ruling, 2026-09-15): the pointer for h-eps0 named OQ-E2, which in this document is the cardinality-semilattice correspondence, the wrong object. The T5 Selection text, the traceability row and the Open Items OQ-A1 cell now point at what ZeroParadox/Ordinal/Incompleteness.lean says: h-eps0 is the alignment hypothesis, and deriving it is open as the Classical.choice inversion conjecture. OQ-E2's own rows are unchanged.
v3.33: DECISION BATCH REMEDIATION AFTER GATE ROUND 2 (Tim rulings, 2026-09-15): T5 selection restated to what snap_unconditional proves: the placement at epsilon-0 is the hypothesis h-eps0 (the ordinal-lattice alignment, open as OQ-E2) and only minimality is derived, carried by both faces of epsilon-0 (supremum of the stages, fundamentalSeq_cofinal; least fixed point, epsilon0_min_eq_max). No rung is ⊥, cited for every rung (Ordinal.epsilon_pos). Iteration: the finite-step sentence is scoped short of a top. Reading gets an antecedent. T5 gloss: Forcing names the shape of each step taken. OQ-A1 short cell two-part; traceability row matches; SnapSuccession cited by full path; join written as vee.
v3.32: DECISION BATCH REMEDIATION ROUND 2 (Tim rulings, 2026-09-15): the OQ-E1 Open Items row called instantiation occurring 'a framework commitment'; it is the occurrence commitment.
v3.31: DECISION BATCH REMEDIATION (Tim, 2026-09-15): T5 box: the selection half ('if the step is taken it is the minimum viable one, alpha_n = eps(S_n), a Conditional Claim given AX-B1's discreteness at every state') is replaced by Tim's confirmed text (ordinal chart: succession_succ, SnapSuccession section I, snap_exactly_at_epsilon_zero, epsilon0_ne_bot; on an arbitrary lattice no step is selected), and the iteration half ('the occurrence commitment applied at each step') by 'No step is guaranteed' (T3, R1, t_snap_irreversible, tsnap_holds_but_nothing_moves) with its epsilon0_min_eq_max reading; the HasFirstStep-at-a-state bullet is removed. R-DA1 points at the box. The Open Items OQ-A1 row reads 'OQ-A1b CLOSED by A1-A4; OQ-A1a answered by crossing charts'; the T5 traceability row and the validation row are synced; 'restated in section VI' is 'DA-1 insert section VI'. The branching-tree implication says the Snap occurring follows from the occurrence commitment together with DA-1 (closed given DP-2).
v3.30: OCCURRENCE COMMITMENT DEFINED, T5 RESTATED, T-SNAP RESIDUE (Tim decision batch, 2026-09-14): the occurrence commitment is ONE commitment, instantiation occurs (a machine configuration reaches P0); DA-1 (closed given DP-2) says a configuration at P0 is executing; together they give that the Snap occurs, and T-SNAP fixes its shape. The canonical AX-1 sentence now reads 'that the snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2)' at the abstract, the Conclusion, R-DA1, the Open Items AX-1 row, the AX-1 traceability and validation rows; premises (ii) names the commitment and DA-1 separately, and hocc is the first-step form of the Snap occurring given CC-1, never of instantiation occurring. The abstract no longer routes the shape through DA-1 ('With DA-1 in place, AX-1 is retired'), and the Binary Snap causality and T-SNAP traceability rows put DA-1 on the occurrence side. T5 (Iterative Forcing Theorem), recovered from ZP-E v1.4, is restated in section VI split the way AX-1 was: selection (if the step from Sn is taken it is the minimum viable one, alpha_n = eps(Sn)) is a Conditional Claim given AX-B1's discreteness at every state, and iteration is the occurrence commitment applied at each step; OQ-A1 is 'closed given AX-B1 and the occurrence commitment', and the T5 traceability row matches. The validation row 'All other ZP-E theorems (T1-T7, T2-C) - Unaffected in content' was false (this document states none of them; T2-C appears nowhere else in it) and now says T1-T4, T6, T7 were stated in ZP-E v1.4 and are not restated here. T-SNAP's box glosses its readable name once: 'Causality' refers to the shape of the step, not to its occurrence. Open Items: 'with no axioms' is 'with no Lean kernel axioms'. The Note on Lean scope was re-checked against Snap.lean and Surprisal.lean and is unchanged. TIM PREVIEW (2026-09-14): the T1-T4, T6, T7 validation row cites an earlier version of this document without naming its version number.
v3.29: T-SNAP PREMISES POINT AT LEAN (Tim, 2026-09-14: pointers plus a small companion). The premises of T-SNAP now have a Lean home: t_snap_given (ZeroParadox/Order/Snap.lean) takes CC-1 (S0 = bottom) and occurrence (S1 != S0) as hypotheses over any join-semilattice with bottom, and t_snap_derived's statement is its MachinePhase instance. Premises of T-SNAP names it in reading (i) and the occurrence hypothesis in (ii); the Status block, Open Items AX-1 row, both traceability rows, the validation row and the endnote point there. CC-1 arc round-4 residue cleared: the section no longer claims to be 'the one place' every other site points to; 'rest on commitments named there' no longer reads as complete; (ii) calls the L-INF step a foundational commitment, as section IV does; the Lean-scope note no longer says 'two decide calls ... bot_join' (one decide, tq_ih its symmetric form, rfl for the join); Step 2 cites DA-1 section IV, not III; DA-2 section I no longer calls the snap 'a structural consequence of reaching P0'; pointers name the DA-1 insert, since DA-2 also has a section V. ROUND 1 GATES (FAIL-BEDROCK, D1) + TIM'S AX-1 SPLIT (Tim, 2026-09-14: 'Both: split it'): reading (i) said t_snap_derived's statement is the MachinePhase instance 'where both hypotheses hold inside the type', which put occurrence inside MachinePhase; the instance is at the chosen sequence c0, c1, c1, ... where hocc reduces to c1 != c0, and the sequence that stays at c0 is a state sequence in the same type that fails hocc. AX-1 bundled the SHAPE of the Snap with its OCCURRENCE: the shape half is Theorem T-SNAP, and the occurrence half was never retired and is the occurrence commitment; the opening, the Conclusion, R-DA1, the Open Items AX-1 row (now SPLIT), both AX-1 retirement rows (the validation row said 'No content lost') and the T5 row are scoped to that. hocc is named occurrence at the first step (a sequence first moving at a later index fails it); t_snap_given takes TWO of the premises, not all; the inequalities restate hocc and only the join is derived (A4); hocc forces at least two points, not exactly two. Also: DA-1 cited at section IV, not III, in section I; the traceability parentheticals attach to T-SNAP, not DA-1; 'NO-GO examples' is 'examples'; 'intended ontological meaning' restated as a reading about the framework's own state sequence. AX-1 WORDING CORRECTED (Tim, 2026-09-14): retired, split into T-SNAP (shape, proved) and the occurrence commitment (stated separately); the earlier 'occurrence half was never retired' was a paraphrase error. ROUND 2 GATES (Tim rulings: title, ZP-C label, DA-1 credit): the Open Items AX-1 row credited the shape to 'P0 + DA-1 + L-RUN + TQ-IH + ZP-A D2', putting DA-1 on the shape side while Premises (ii) puts it on the occurrence side; it now carries Tim's sentence: the shape is proved as T-SNAP from L-RUN, TQ-IH and the bottom law with no axioms, and occurrence is the occurrence commitment, which DA-1 argues for. That row and the AX-1 retirement validation row equated the occurrence commitment with hocc; both now say hocc is its first-step form, as (ii) does. Reading (i) said the start at bottom is built into the choice of the type MachinePhase; a state sequence in that type can start at c1, so the start comes from the statement's choice of c0, and only binary existence is in the type.
v3.28: CC-1 STATUS SYNC (Tim, 2026-09-13: everything in one arc). "CC-1 derived / closed / no longer a freestanding commitment" collapsed two readings: cc1_derived proves the CONDITIONAL (a state sequence starting at a Quine atom starts at bottom), and with t_exec_iff the converse holds, so the starting-point choice is RESTATED through the Quine-atom role, not forced; every ZP-A lattice carries AFAStructure trivially. Every site now keeps both halves, matching ZP-J v2.7. Also CC-2 no longer called 'a structural consequence' (bot_self_mem is a class FIELD T-EXEC consumes): it is ZP-A's Forced Metatheoretic Commitment, T-EXEC proves bottom the only occupant of the Quine-atom role, and in AFA set theory Q = {Q} is a theorem while bottom being that set is the argued step. DA-1 Path 1's 'bottom in bottom, i.e. bottom = {bottom}' reversed to the true direction and its 'not a commitment - forced' restated as argued (more than a free choice, less than a theorem); the iff is t_exec_iff. ADVERSARY ROUND 1 (FAIL-BEDROCK, D1): the T-SNAP Status block still dropped CC-1 from T-SNAP's givens ('derived given DA-1 and AX-B1') on the strength of 'neither freestanding', while the DA-1 Status block four paragraphs earlier lists 'DA-1, CC-1, and AX-B1'; the premise that dropped it was the retracted derivation, so CC-1 is restored to the givens and called a Conditional Claim. The DA-1 synthesis paragraph's 'establishing bottom = {bottom} as a structural consequence rather than a commitment (ZP-J T-EXEC)' was the CC-2 site this entry's sweep missed; it now matches Path 1. ROUND 1 (editorial + claim-review + adversary FAIL-BEDROCK; prior-art PASS): the sync first gave the wrong REASON for "not forced" ("every ZP-A lattice carries AFAStructure trivially, so ..."), which does not follow; the reason is that a valid state sequence can start above bottom (T2 fixes only bottom <= S0; an example on OntologicalStates in OntBridge.lean). Also R-AFA and Path 1 say T-EXEC proves the Quine-atom role's occupant is bottom, not that it 'formally verifies the structure' or checks 'the structural self-application fixed point'; Path 1's executes-itself step no longer jumps silently to 'its own sole member' (Aczel's 0* = {empty, 0*} contains itself without being its own singleton); Q = {Q} cited to Aczel 1988 Example 1.3. GATE ROUND 2 (ordinary, carried): the 'not forced' reason needs its scope - on a ONE-point lattice every sequence starts at bottom, so the countermodel is stated for a lattice with a second point, and the OntBridge.lean example now also shows the start is not a Quine atom. T-SNAP PREMISE LISTS RECONCILED (Tim: fold into this arc; ZPE-TSNAP-PREMISES): the informal argument uses AX-B1 at Step 4 and CC-1 for the start at bottom, while the box, the Status block and the validation row each listed a different subset; all now say derived given the commitments AX-B1 and CC-1, and CC-1 no longer shares 'the same logical status as named axioms'. The Lean t_snap_derived is unaffected: it takes no hypotheses and no axioms. CLAIM-REVIEW ROUND 3 (FAIL-BEDROCK, D1): the reconciled lists were each one short - the box's 'given two commitments', the Status block's 'Commitments: AX-B1; CC-1' and the validation row's 'Every other dependency is a closed theorem' omitted that Step 2 imports DA-1, closed only given DP-2, and that occurrence is a commitment (tsnap_holds_but_nothing_moves satisfies AX-B1 and CC-1 and never moves). No fourth hand list: the premises are now stated ONCE, as 'Premises of T-SNAP, in two readings' after the Theorem box - (i) the Lean form, no hypotheses, fixes the shape on MachinePhase; (ii) the prose argument uses AX-B1 and CC-1 among its commitments, and occurrence rests further on DA-1 given DP-2 and the occurrence commitment - and the box, both status blocks, the validation row and the Remaining-axioms row point there without a count.
v3.27: C-DA2 RETRACTION COMPLETED (bedrock). v3.26 downgraded the Corollary to a Conditional Claim and rewrote its section, but the Validation Status table's STATUS cell was never touched - it still shipped "Valid - Derived. Follows directly from DA-2 and ZP-B C3." four pages after the section saying the opposite, on the one page a reader opens specifically to check status. A half-applied fix to a self-consistent error manufactures a self-contradiction; the wording now matches the dependency table, which had it right at :786 all along.
Zero Paradox — ZP-E: Bridge Document PDF Builder
Version 3.26 | July 2026
v3.26: NOVELTY OVERCLAIM RETRACTED (bedrock) - C-DA2 DOWNGRADED FROM COROLLARY TO CONDITIONAL CLAIM. The document published "Corollary C-DA2 - Ontological Novelty of Successive bottom" with a status cell reading "Derived - Corollary of DA-2 and C3" and a written proof whose load-bearing step - "the bottom of I_{n+1} is an element of a distinct topological space" - IS the conclusion, not a consequence of C3. C3 quantifies over paths WITHIN one space; it is silent on whether the next instantiation's space is a different one, so assuming separateness to derive distinctness is circular. The handle C-DA2 is unchanged per R-NAMING; only its STATUS changes. Measured against: snap_arc_z2_loop proves the 2-adic tower starts at 0, every finite stage is nonzero, and it converges back to 0, and tower_image_loops_to_seed states the limit IS the seed - so in that chart novelty does not merely lack a proof, it fails. Also fenced at the TrackedOutput return, the DA-2 connection, the no-back-edges bullet, the DA-2 traceability row and both status tables. v3.25 retracted the OCCURRENCE overclaim and left NOVELTY standing beside it.
v3.25: FORCING OVERCLAIM RETRACTED. The document asserted that T-SNAP establishes the snap OCCURS. It does not: T-SNAP fixes the transition's shape, and Order/Snap.lean's NO-GO gauge tsnap_holds_but_nothing_moves proves T-SNAP holds in a model where nothing moves. Occurrence is a framework commitment (Information/Surprisal.lean's l_inf docstring is the designated honest stopping point). Prose only; no claim gains support and none is withdrawn beyond this one. Four sites: the branching-tree implication, the OQ-E1 row, and two claim-table validity grounds, all of which used occurrence as the ground. OQ-E1 is now 'closed given the occurrence commitment', matching CLAIMS.md and the DA-1 row's existing 'closed given DP-2' form.
v3.24: R-AFA false premise corrected (bedrock) — struck the invalid "well-founded ⟹ finite ∈-tree / finite ∈-rank ⟹ finitely interpretable" step (false: ω is well-founded and infinite). Foundation-incompatibility now rests on the self-membership of ⊥ = {⊥} (Regularity; no_quine_atom, choice-free), with R3/L-INF demoted from independent proofs to corroboration. Status brought current: forcing + realizability stated as machine-checked (QuineHost — quineHost_not_wellFounded, oneAtom_not_wellFounded, afaStructure_isQuineHost); CC-2 = Forced Metatheoretic Commitment, not Conditional Claim; named falsifier narrowed to the requirements-choice. Also CC-1 "modelling commitment" → "derived via ZP-J cc1_derived" (DA-2); DA-3 cardinality-anomaly link hedged to conjecture (DA-3-C1 / OQ-E2); closing endnote rewritten from editorial-history narration to a description of what the document is.
v3.23: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v3.21: FMC precision (sweep Step 4 remediation, against fmc.md) — R-AFA "the metatheoretic necessity of AFA is derived" → "argued, not proved (a metatheoretic squeeze, not a derivation)"; named falsifier added to R-AFA; CC-2 status lines now split the proved structural fixed point (T-EXEC, axiom-free) from the argued set-membership reading; "establish that Foundation is incompatible" → "make the case that".
v3.20: Rendered version refs removed — DA-2/DA-3 section notes ("New in v2.0") and endnote version (C1 sweep — no version changelogs in rendered PDF content).
v3.19: Version reference removed from T-BUF li() call (Gemini catch — build gate does not cover li()).
v3.18: Vocabulary fixes — "null state" → "⊥"; "non-null state" → "nonzero state" throughout body prose; version references (v1.4, v1.5, v2.7, v1.0) removed from body prose. Palette rebuild.
v3.17: K-22 vocabulary fix — "informational extremity" → "unbounded surprisal (L-INF)"
in DA-1 Section II bridge prose.
v3.16: Version numbers removed from three internal register section headers (Open Items,
Traceability, Validation Status) — version numbers belong in the title block only.
v3.15: DA-1 Path 2 forward reference to ZP-M R-M.1 added at three locations — retrospective
structural analysis of why the informational bridge resisted formalization.
v3.14: Adversary-review pass — "AX-1 is promoted" → "AX-1 is derived as" (two occurrences);
version history removed from opening paragraph (belongs in docstring); "[AX-1 Promoted to
Theorem]" bracket removed from theorem box title; "structural event" → "structural limit";
Section VII headers renamed from grand-scope vocabulary to mathematical descriptions:
"Multiverse as structural implication" → "Structural Implication: Branching Tree Structure";
"Free will and irreversibility" → "Monotonicity and Path Irrecoverability";
"Time's arrow" → "Ordinal Direction of State Sequences".
v3.13: Precision fix — "topological isolation is maximal" replaced with "clopen separation is
total — 0 and every nonzero element lie in disjoint clopen classes" (0 in ℚ₂ is not topologically
isolated; the correct property is clopen separation). "DA-1 unifies" replaced with "DA-1
establishes these as descriptions of the same structural event across four independent
mathematical languages."
v3.12: Framework scope and failure-mode framing added to preamble — "coverage not exhaustion"
paragraph addresses the "why these four?" question; cross-framework failure-mode paragraph names
the domain-specific limit at ⊥ for each layer (lattice minimum, p-adic isolation, unbounded
surprisal, orthogonal basis vector) and positions DA-1 as the unifying argument.
v3.11: T-SNAP Step 7 corrected — AX-G2 removed as formal dependency; now labelled as conceptual
correspondence only. ZP-G is downstream of ZP-E and cannot be a formal dependency of T-SNAP.
Irreversibility proof rests on ZP-A R1 and ZP-B C3 alone, which are sufficient.
v3.10: Forward references to "ZP-PQ" replaced throughout with "The Philosophical Question That Started This" — that document already contained the dissolution argument; ZP-PQ was always a placeholder label.
v3.9: R-ε₀ reframed — remark now leads with explicit informal-analogy disclaimer; "structural
correspondence" changed to "structural analogy" throughout R-ε₀. Reviewer feedback: hedge was
buried at end of remark; readers might miss it after several paragraphs of parallel-drawing.
v3.8: DA-1 Path 2 recharacterized — from "outside Lean scope (informational bridge)" to
"foundational commitment: a missing principle, not a missing proof." No computability library
closes the gap between 'system at P₀' and 'system is running.' Forward paths: new axiom,
Chalmers' implementation notion, or The Philosophical Question That Started This. That document already contains
the dissolution: the description-instantiation gap assumes a separability the framework dissolves.
v3.7: DA-1 formally closed via ZP-K — KleeneStructure MachinePhase instance proved in Lean 4.
da1_closed_concrete : IsQuineAtom (bot : MachinePhase). DA-1 Path 1 (structural/AFA) and
Path 3 (computational/Kleene) now in Lean scope. Path 2 (informational bridge) remains outside
Lean scope. "Outside Lean Scope" designation removed from ZPE.lean DA-1 section.
v3.6: DA-1 Path 1 rewritten — argument direction reversed. Previously: CC-2 (⊥ = {⊥}) asserted,
then "no external interpreter" derived. Now: "nothing external to ⊥ can execute ⊥" argued first,
⊥ = {⊥} derived as the only coherent structure, ZP-J T-EXEC cited as formal verification.
CC-1 and CC-2 status updated throughout — no longer freestanding commitments; both derived via ZP-J.
v3.5: Open Items Register DA-1 status updated — "CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT
(corroboration of precondition)" now matches v3.3 path-hierarchy framing.
v3.4: R-AFA minimality argument made explicit — added one sentence to "What remains
conditional" stating that ⊥ = {⊥} is uniquely minimal among AFA non-well-founded sets:
exactly one member, no internal differentiation; any extension exceeds A4's constraint.
v3.3: DA-1 path hierarchy foregrounded — added explicit framing before Paths 1–3 stating
that the three informal paths are corroboration of the precondition DP-2 formalizes, not
parallel proofs of DA-1 itself. Shrinks attack surface on Angle 1 (DA-1 doing too much work).
v3.2: Remark R-AFA added — Foundation ruled out by R3 and ZP-C L-INF; AFA identified as the
forced metatheoretic replacement rather than an arbitrary choice; CC-2 status clarified.
v3.1: Remark R-ε₀ added — notation justification for ε₀ symbol choice; structural correspondence
with the Cantor-Gentzen proof-theoretic ordinal explained.
v3.0: DP-2 (Execution Distinguishability) added — DA-1 formally grounded in TrackedOutput construction
(ZPE.lean §VI); da1_minimal_path proved axiom-free in Lean. First Lean formalization of DA-1,
conditional on DP-2. Section III (DP-2) inserted in DA-1 insert; existing III/IV/V renumbered IV/V/VI.
v2.9: DA-1 Lean scope note added — functional role carried by ZPC.l_run/tq_ih; AIT+ZF+AFA bridge
outside Lean scope (same category as ZP-A CC-2). PDF status line updated to reflect Lean scope.
v2.8: DA-1 formal bridge added: incompressibility = self-description argument (ZP-C D1 + standard AIT).
At P0, K(c1|n)/|c1| = 1 means description and execution coincide; CC-2/R3 and L-INF become corroboration.
v2.7: DA-1 upgraded from Design Principle to Derived Proposition — grounded in ZP-A CC-2 and R3.
Follows all rules in pdf rendering standards:
  - DejaVu fonts only
  - Checkmark always wrapped in <font name="DV">
  - All table cells are Paragraph objects
  - No unicode subscripts — use sub/super tags
  - US Letter, 1-inch margins, TW = 6.5 inch
"""

import os
from zp_utils import *

VERSION = '3.45'
FIRST_RELEASED = 'April 2026'

# ── Local overrides: ZP-E uses justified body text ────────────────────────────
S['body']    = ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14, spaceAfter=6, alignment=4)
S['bodyI']   = ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14, spaceAfter=6, alignment=4)
S['li']      = ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14, leftIndent=18, spaceAfter=3, alignment=4)
S['derived'] = ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14, spaceAfter=6, textColor=GREEN_DARK, alignment=4)

bridge_box = remark_box  # SLATE header — ZP-E bridge document style


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-E_Bridge_Document.pdf')
    print(f'[build_zpe] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-E: Bridge Document', 'ZP-E: Bridge Document', 'Version ' + VERSION)
    E   = []

    print('[build_zpe] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-E: Bridge Document', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document is the cross-framework synthesis layer of the Zero Paradox. It imports from '
        'ZP-A (lattice algebra), ZP-B (p-adic topology), ZP-C (information theory), and ZP-D (Hilbert '
        'space state layer). It provides three formal inserts: DA-1 (Instantiation as Execution), '
        'DA-2 (Instantiation Succession), and '
        'DA-3 (Perspective-Relative Cardinality). AX-1 (Binary Snap Causality) is retired. Its content was split in two: '
        'the shape of the snap is proved, as Theorem T-SNAP, and that the snap occurs is stated separately: it follows from '
        'the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
        'tsnap_holds_but_nothing_moves shows T-SNAP does not carry it. With DA-2, the directed instantiation tree is formally licensed. With DA-3, '
        'cardinality is shown to be position-dependent within the instantiation structure.'))
    E.append(body(
        'Illustrated Companion: A paired ZP-E Illustrated Companion document provides accessible '
        'explanations and visual summaries of the bridge derivations in this document. Readers new '
        'to the framework are encouraged to start with the companion.',
        style='bodyI'))
    E.append(body(
        '<b>A note on framework scope.</b> The four layers (ZP-A through ZP-D) are not claimed to be '
        'the only mathematical domains in which the Zero Paradox structure appears. They are chosen '
        'because they cover the canonical mathematical languages for describing state: algebraic order '
        'structure (ZP-A), topology and metric geometry (ZP-B), information and complexity theory (ZP-C), '
        'and functional/Hilbert space analysis (ZP-D). The claim is that the same structural '
        'limit appears across each of the four frameworks addressed here — not that these four '
        'are the only possible witnesses.'))
    E.append(body(
        'Across all four layers, the same structural limit appears at &#8869; — but each framework names '
        'it differently: ZP-A identifies &#8869; as the global minimum, below which the lattice\'s ordering '
        'relation cannot descend; ZP-B finds the p-adic valuation undefined (or +&#8734;) at 0, where '
        'clopen separation is total — 0 and every nonzero element lie in disjoint clopen classes; '
        'ZP-C finds surprisal unbounded above at &#8869;, so no finite '
        'external description can contain &#8869;; ZP-D maps 0 to a basis vector orthogonal to '
        'every nonzero state, from which no return is possible. DA-1 establishes these as descriptions '
        'of the same structural limit across four independent mathematical languages.'))
    E.append(hr())

    print('[build_zpe] Building DA-1...')
    # ── FORMAL INSERT DA-1 ────────────────────────────────────────────────────
    E += [
        Paragraph('Formal Insert DA-1: Derived Proposition — Instantiation as Execution', S['h1']),
        Paragraph('<i>DA-1 is a Derived Proposition: instantiation as execution, the first Lean '
                  'formalization of DA-1 (axiom-free, conditional on DP-2, Snap.lean &#167;VI), with '
                  'incompressibility read as self-description (ZP-C D1 + AIT) and CC-2/R3 grounding.</i>',
                  S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-1 Closes', S['h2']))
    E.append(body('The T-BUF chain from ZP-C established three results:'))
    E += [
        li('L-RUN: The transition c<sub>0</sub> → c<sub>1</sub> is a nonzero state transition. (ZP-C — Derived)'),
        li('TQ-IH: No program outputs ⊥ without a nonzero intermediate configuration state. (ZP-C — Derived by L-RUN)'),
        li('T-BUF: At P<sub>0</sub>, execution is structurally guaranteed; that execution state is ε<sub>0</sub> in the semilattice. (ZP-C — Candidate Theorem pending DA-1)'),
        sp(4),
    ]
    E.append(body(
        'T-BUF was labelled Candidate because Step 2 asserts that a configuration at P<sub>0</sub> is a '
        'live machine state — that instantiation at P<sub>0</sub> constitutes an execution event, not a static '
        'description. ZP-C L-INF supplies one mathematical premise: &#8869; at P<sub>0</sub> has unbounded '
        'surprisal — no finite external interpreter can hold it as a static description. ZP-A CC-2 '
        'supplies a second, structural basis: &#8869; = {&#8869;} is a self-containing object with no external '
        'interpreter by structure. DA-1 (&#167; IV below) provides the derived proposition that closes T-BUF Step 2.'))

    E.append(Paragraph('II. The Two Senses of a Configuration at P<sub>0</sub>', S['h2']))
    E += [
        Paragraph(
            fix('Sense A — Descriptive: x exists as a string — a finite syntactic object that has been written '
                'down or specified. The machine it describes has not necessarily been instantiated. P<sub>0</sub> is a '
                'property of the string. The string is inert.'),
            S['li']),
        sp(4),
        Paragraph(
            fix('Sense B — Instantiated: x exists as the current configuration of a running machine. The '
                'machine is executing. P<sub>0</sub> is a property of the live configuration. The configuration is active.'),
            S['li']),
        sp(6),
    ]

    E.append(Paragraph('III. Design Principle DP-2 — Execution Distinguishability', S['h2']))
    E.append(body(
        'The two senses of § II share the same output value (⊥) but differ in machine state. '
        'This separation — output value is not machine state — is made precise by Design Principle DP-2.'))
    E.append(bridge_box(
        'Design Principle DP-2 — Execution Distinguishability',
        [
            'Machine states carry execution history independently of output values. '
            'A machine in state c<sub>1</sub> can output ⊥ (the null value) while being in a configuration '
            'entirely distinct from a machine in state c<sub>0</sub>. The post-execution null and the '
            'pre-execution null are different instances — same output value, different machine state.',
            'Lean formalization (Snap.lean &#167;VI): TrackedOutput separates value : MachinePhase '
            'from state : MachinePhase. preInstantiation = &#10216;c<sub>0</sub>, c<sub>0</sub>&#10217;; '
            'postInstantiation = &#10216;c<sub>0</sub>, c<sub>1</sub>&#10217;. '
            'Theorem dp2_execution_distinguishability proves: '
            'preInstantiation.value = postInstantiation.value (same output) ∧ '
            'preInstantiation.state ≠ postInstantiation.state (distinct machine states). '
            'Proved axiom-free.',
        ]
    ))
    E += [
        sp(4),
        body(
            'Given DP-2, DA-1 is Lean-formalizable at the minimal-path level. '
            'Theorem da1_minimal_path (Snap.lean &#167;VI) establishes four conjuncts: '
            '(1) before and after instantiation, the output value is the same (⊥); '
            '(2) the machine states are distinct (c<sub>0</sub> ≠ c<sub>1</sub>); '
            '(3) the machine was at c<sub>0</sub> before; '
            '(4) the machine is at c<sub>1</sub> after. '
            'Proved axiom-free — no Kolmogorov complexity, no ZF+AFA required. '
            'The "return to null" after instantiation is postInstantiation (output ⊥, state c<sub>1</sub>) — '
            'not preInstantiation (output ⊥, state c<sub>0</sub>). '
            'Irreversibility (ZPB C3, ZPE t_snap_irreversible) blocks any path back to preInstantiation.'),
    ]

    E.append(Paragraph('IV. Proposition DA-1', S['h2']))
    E.append(bridge_box(
        'Proposition DA-1 — Instantiation as Execution',
        [
            'Claim: The instantiation of a machine configuration c<sub>1</sub> at the incompressibility threshold '
            'P<sub>0</sub> is an execution event in the sense of L-RUN. It is not a static description of a machine. '
            'It is a machine in state c<sub>1</sub>.',
            'Formal core (Lean): DP-2 (§III) — TrackedOutput separates output value from machine state. '
            'da1_minimal_path proves: one act of instantiation moves c<sub>0</sub> to c<sub>1</sub> regardless '
            'of output value. The returned ⊥ occupies the bottom role again; reading it as a NEW null rather than the prior c<sub>0</sub> is C-DA2, a modelling commitment. The axiom-free result is the role, not the novelty.',
            'Structural grounding: ZP-A CC-2 (⊥ = {⊥}) establishes ⊥ as a Quine atom under ZF + AFA — a set that is '
            'its own singleton, admitting no external interpreter. ZP-A R3 derives the immediate consequence: '
            'a self-containing object cannot be a static description awaiting external instantiation. '
            'ZP-C L-INF provides independent informational corroboration: ⊥ has unbounded surprisal, '
            'exceeding the capacity of any finite interpreter.',
        ]
    ))
    E += [
        sp(4),
        body('The three paths below are not parallel proofs of DA-1. Each argues independently for why '
             'the precondition DP-2 formalizes holds — why instantiation of &#8869; at P<sub>0</sub> '
             'necessarily constitutes a first instruction fetch rather than a static description. '
             'DP-2 + da1_minimal_path derive c<sub>0</sub> &#8594; c<sub>1</sub> axiom-free once that '
             'precondition is established. The paths are convergent corroboration of the precondition; '
             'the formal derivation is DP-2\'s.'),
        body('Path 1 — Structural (Self-Execution, ZP-J T-EXEC): Nothing exists outside the null space. '
             '&#8869; is prior to all differentiation — there is no external state, no prior cause, no position '
             'from which something else could execute &#8869;. If &#8869; executes at all, the only possible '
             'executor is &#8869; itself. A thing that executes itself contains itself, and the framework reads this as its own sole member: '
             '&#8869; = {&#8869;}, so &#8869; &#8712; &#8869;. The argument is that this is forced by the impossibility of external '
             'execution, which makes it more than a free choice and less than a theorem. ZP-A R3 states the structural consequence: a self-containing object admits no external '
             'interpreter position. ZP-J T-EXEC proves that whatever fills the Quine-atom role is &#8869;: IsQuineAtom(q) &#8596; q = &#8869;, '
             'proved axiom-free in Lean 4 (ZeroParadox.t_exec_iff). AFA (ZF + AFA) is <i>a</i> consistent '
             'set-theoretic home for this structure, and the commitment is not the <i>adoption of AFA '
             'specifically</i>: it is a set of requirements on the host theory &#8212; that the bottom is a '
             'self-containing Quine atom (&#8869; = {&#8869;}), and that this atom is unique &#8212; of '
             'which AFA is the canonical example. '
             'ZP-A CC-2 (&#8869; = {&#8869;}) is a Forced Metatheoretic Commitment: on a lattice, T-EXEC proves that '
             'whatever fills the Quine-atom role is &#8869; (axiom-free, given the field bot_self_mem); in AFA set theory Q = {Q} is a theorem (Aczel 1988, Example 1.3), and that the framework&#8217;s &#8869; is that set is the argued metatheoretic step (see Remark R-AFA).'),
        body('Path 2 — Informational (ZP-C L-INF): Independently, the surprisal I(n) = n at ball-hierarchy '
             'depth n is unbounded — for any finite M, ∃ depth n with I(n) > M. ⊥ corresponds '
             'to the limit point 0 ∈ Q<sub>2</sub>; its informational content exceeds every finite bound. '
             'Any finite external interpreter can hold only a finite informational bound; ⊥ exceeds every '
             'such bound. '
             'Note: Path 2 is motivational context, not a formal path to the conclusion. The step '
             '"exceeds every finite bound → therefore necessarily executing" is a foundational commitment, '
             'not a derivable claim. It asks what it means for a mathematical structure to <i>instantiate</i> '
             'rather than merely <i>satisfy</i> conditions — a question no computability library answers. '
             'Forward paths: (a) a new axiom explicitly committing to this bridge; (b) a connection to '
             'Chalmers\' notion of implementation; (c) the dissolution argument in The Philosophical Question That Started This — the separability '
             'of description and instantiation is the assumption the framework dissolves, not a gap it must '
             'close from the outside.'),
        body('Path 3 — Formal bridge: Incompressibility as Self-Description (ZP-C D1 + standard AIT): '
             'The preceding paths establish that ⊥ admits no external interpreter. This path provides '
             'the formal bridge from that negative claim to the positive claim (necessarily executing). '
             'In the standard Turing model (D7), a machine configuration x exists in one of two states: '
             '(A) Static description — x exists as a string specified but not yet being executed; some '
             'external program p (|p| &lt; |x|) generates x when run, so x is a description awaiting a '
             'separate execution event by an external generator. '
             '(B) Live execution — x is the current configuration of a running machine. '
             'These are exhaustive in the Turing model: either x has a shorter external generator, or it does not. '
             'At P<sub>0</sub>, ZP-C D1 gives K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1: c<sub>1</sub> is algorithmically incompressible. '
             'No external program p exists with |p| &lt; |c<sub>1</sub>| such that U(p, n) = c<sub>1</sub>. '
             'State (A) requires such a p — and no such p exists at P<sub>0</sub>. '
             'State (A) is therefore eliminated by the Kolmogorov condition. '
             'Since (A) and (B) are exhaustive and (A) is eliminated, c<sub>1</sub> is in state (B): it is executing. '
             'Instantiation at P<sub>0</sub> is not the placement of a description to be executed later — '
             'there is no shorter prior description to execute. Given DP-2, instantiation and execution are the same act (DA-1).'),
        body('The formal grounding (DP-2, §III) and the three paths above operate at distinct levels, '
             'not as alternatives to one another. DP-2 + da1_minimal_path establish a conditional at the '
             'level of machine-state representation: <i>if</i> instantiation of ⊥ constitutes a first '
             'instruction fetch in the sense of D7, <i>then</i> c<sub>0</sub> → c<sub>1</sub> follows '
             'necessarily — axiom-free, proved by construction. DP-2 is grounded in D7 itself (the standard '
             'computational distinction between before-first-instruction and after-first-instruction states), '
             'which is prior to and independent of DA-1. The three paths above operate one level down: they '
             'argue for why the precondition holds — why instantiation of ⊥ necessarily constitutes a first '
             'instruction fetch at all. Path 1 (structural) argues that nothing external to &#8869; can '
             'execute &#8869; — therefore &#8869; must execute itself, which argues for &#8869; = {&#8869;} as '
             'more than a free choice and less than a theorem (ZP-A CC-2, a Forced Metatheoretic Commitment); '
             'ZP-J T-EXEC proves, axiom-free, that whatever fills the Quine-atom role is &#8869;. Path 2 (informational) '
             'provides motivational context — unbounded surprisal as a pointer toward why static holding is '
             'incoherent — but the bridge from unbounded surprisal (L-INF) to execution is a foundational '
             'commitment, not a derived claim. Path 3 (AIT) argues that incompressibility eliminates the '
             'static-description alternative. '
             'Path 1 is witnessed by da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
             'computational; Path 3&#8217;s witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
             'requirement, not a second independent proof. The two are carried together by da1_paths_unified as a conjunction of '
             'witnesses; that they name one structural fact is the framework&#8217;s reading. Path 2 identifies a missing principle; '
             'its forward resolution is in The Philosophical Question That Started This. Path 2 is context. '
             '(ZP-M R-M.1 provides a retrospective structural analysis of why the gap resisted formalization.)'),
        derived('Status: DERIVED PROPOSITION — primary formal grounding: DP-2 (§III, TrackedOutput construction). '
                'da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI): instantiation moves c<sub>0</sub> '
                'to c<sub>1</sub> regardless of output value. ✓ '
                'Path 1 (structural, ZP-J T-EXEC + ZP-K): witnessed by da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase), proved in Kleene.lean, which proves nothing computational. '
                '(Under MachinePhase\'s selfMem x := x = &#8869;, this reduces to (&#8869; = &#8869;) &#8743; (&#8704; x, x = &#8869; &#8658; x = &#8869;) — structural closure enforced by typeclass design, not a set-theoretic derivation from ZF+AFA. See R-K.0.) '
                'Path 2 (informational, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a missing proof. Forward: The Philosophical Question That Started This; ZP-M R-M.1 (retrospective structural analysis). '
                'Path 3 (computational, ZP-K Kleene): its witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field — a KleeneStructure requirement, not a second independent proof; da1_paths_unified carries it with Path 1 as a conjunction of witnesses. '
                'CC-1 (S<sub>0</sub> = &#8869;): restated — ZP-J cc1_derived with t_exec_iff makes a Quine-atom start and a &#8869; start the same condition (axiom-free, Lean) — and not forced: on a carrier with a second point a valid sequence starts elsewhere (ZeroParadox/Settheory/OntBridge.lean). '
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; is the AFA set Q = {Q} is an argued metatheoretic commitment (see R-AFA). '
                'DP-2 (&#167;III) — explicit. '
                'T-SNAP&#8217;s premises, in its Lean form and in its prose argument, are stated under Premises of T-SNAP (DA-1 insert, &#167; V). '
                'AIT (Kolmogorov complexity) outside Lean scope; the Kleene structure is its in-scope counterpart, carried as a KleeneStructure requirement (botCode_is_quine), not a proof of the AIT claim.'),
    ]

    E.append(Paragraph('V. Theorem T-SNAP — Binary Snap Causality', S['h2']))
    E.append(bridge_box(
        'Theorem T-SNAP — Binary Snap Causality',
        [
            '&#8220;Causality&#8221; in this name refers to the shape of the step, not to its occurrence.',
            'Statement: The Binary Snap ⊥ → ε<sub>0</sub> is a derived consequence of P<sub>0</sub>, L-RUN, TQ-IH, '
            'DA-1, and ZP-A D2, among the results the seven steps below cite. It is not an axiom. '
            'What it rests on differs between its Lean form and its prose argument: see Premises of T-SNAP, directly below.',
        ]
    ))
    E += [
        sp(4),
        body('<b>Premises of T-SNAP, in two readings.</b> Both readings are true, and neither replaces the other. '
             'In Lean, two of the premises, CC-1 and occurrence at the first step, are the hypotheses of t_snap_given, named in (i).'),
        li('(i) <i>Lean form: the shape.</i> t_snap_derived : c&#8320; &#8800; c&#8321; &#8743; c&#8321; &#8800; c&#8320; &#8743; '
           'join c&#8320; c&#8321; = c&#8321; (ZeroParadox/Order/Snap.lean) takes no hypotheses, and &#35;print axioms reports no axioms. '
           'It is a fact about the fixed two-state type MachinePhase, with the initial phase c&#8320; as its bottom element &#8869; and the running phase c&#8321; above it: '
           'the two phases differ, and joining them gives c&#8321;. Nothing is passed to it as an argument; binary existence is '
           'built into the choice of that type, and the start at &#8869; into the statement&#8217;s choice of c&#8320;. It fixes the SHAPE of the transition, not that one occurs: tsnap_holds_but_nothing_moves proves '
           'the same statement in a dynamics where every phase is a fixed point. '
           'Two of the premises as hypotheses: t_snap_given (same file) holds over any join-semilattice with bottom, taking '
           'S&#8320; = &#8869; (hcc1, CC-1) and S&#8321; &#8800; S&#8320; (hocc, occurrence at the first step: the step at index 1 is taken) '
           'and giving the same shape at S&#8320;, S&#8321;. Its two inequalities restate hocc; only the join conjunct is derived, from A4. '
           't_snap_derived&#8217;s statement is its MachinePhase instance at the sequence c&#8320;, c&#8321;, c&#8321;, &#8230;, where hcc1 holds by rfl '
           'and hocc reduces to c&#8321; &#8800; c&#8320;. MachinePhase does not discharge occurrence: the sequence that stays at c&#8320; is a '
           'state sequence in the same type and fails hocc. With no '
           'dynamics given, dropping either hypothesis makes the conclusion fail (examples beside it). hocc forces at least two '
           'points and does not force exactly two; AX-B1&#8217;s discreteness is not in that signature.'),
        li('(ii) <i>Prose argument: the shape, then the occurrence.</i> The seven steps below read that shape as a statement about the '
           'framework&#8217;s own state sequence. That reading uses commitments, among them AX-B1 (binary existence, ZP-B, the framework&#8217;s one '
           'substantive modelling commitment) at Step 4, and CC-1 (S<sub>0</sub> = &#8869;, a ZP-A Conditional Claim) for the start at &#8869; in Steps 4 and 6. '
           'That the transition OCCURS rests further on two things. The occurrence commitment: instantiation occurs (a machine configuration reaches P&#8320;). '
           'And Step 2, which imports DA-1: a configuration at P&#8320; is executing. DA-1 is closed only given DP-2: &#167; IV derives c&#8320; &#8594; c&#8321; from DP-2 '
           'once DP-2&#8217;s precondition is established, and calls its three paths convergent corroboration of that precondition; Path 1 argues through '
           'ZP-A CC-2, itself a commitment. Together they give that the Snap occurs, which is not a theorem. Given CC-1, its first-step form is the hypothesis hocc of t_snap_given '
           '(a sequence that first moves at a later index fails hocc). ZP-C L-INF '
           'supplies unbounded surprisal, and the step from there to forced execution is a foundational commitment (&#167; IV), not a '
           'mathematical consequence of L-INF alone.'),
        sp(4),
        body('Proof:'),
        body('<i>Note on Lean scope: the formal Lean proof of T-SNAP is a single term — '
             '&#10216;l_run, tq_ih, rfl&#10217; — l_run proves c&#8320; &#8800; c&#8321; by decide, tq_ih is its symmetric form, '
             'and rfl closes the join in the MachinePhase semilattice (t_snap_given obtains that conjunct from A4, bot_join). '
             'What follows is the informal motivation for the modelling choices that let that term '
             'be read as a statement about the framework&#8217;s own state sequence.</i>'),
        sp(4),
        li('Step 1 — P<sub>0</sub> identifies the incompressibility threshold. When K(x|n)/n = 1, the configuration string x is algorithmically random. (ZP-C D1)'),
        li('Step 2 — A configuration at P<sub>0</sub> is necessarily executing: At P<sub>0</sub>, K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1 (ZP-C D1) — c<sub>1</sub> is incompressible, its own minimal program. No shorter external generator exists; the static description state is eliminated; c<sub>1</sub> is in live execution (DA-1 Path 3 — from ZP-C D1 + AIT). Corroboration: ⊥ = {&#8869;} (ZP-A CC-2/R3); unbounded surprisal (ZP-C L-INF). (DA-1 &#167; IV — Derived Proposition)'),
        li('Step 3 — Any instantiated execution passes through c<sub>1</sub>. (ZP-C D7 — definitional; c<sub>1</sub> is the first running configuration)'),
        li('Step 4 — c<sub>1</sub> ≠ ⊥. (ZP-C L-RUN — Derived; c<sub>1</sub> has gained execution context not present in c<sub>0</sub> = ⊥; by AX-B1 this is a distinct, nonzero state)'),
        li('Step 5 — No program that executes produces only ⊥ configuration states. (ZP-C TQ-IH — Derived; execution trace τ(p) contains c<sub>1</sub> for any executing program p)'),
        li('Step 6 — In (L, ∨, ⊥), c<sub>1</sub> is an element strictly above ⊥. By ZP-A D2, the transition ⊥ → c<sub>1</sub> is a valid state transition: c<sub>1</sub> = ⊥ ∨ ε<sub>0</sub> for some ε<sub>0</sub> ∈ L with ε<sub>0</sub> > ⊥. This transition is the Binary Snap.'),
        li('Step 7 — The transition is irreversible: algebraically by ZP-A R1 (no subtraction operator); topologically by ZP-B C3 (no continuous return path to 0 in Q<sub>2</sub>). These two grounds are sufficient. Conceptual correspondence: ZP-G AX-G2 (hom(X, 0) = ∅ for X ≠ 0) expresses the same irreversibility in categorical language — ZP-G is downstream of ZP-E and is not a formal dependency of this proof.'),
        sp(4),
        body('Conclusion: The Binary Snap is a derived consequence, given the commitments under Premises of T-SNAP. '
             'AX-1 (Binary Snap Causality) is retired. Its content was split in two: the shape of the snap is proved, '
             'as Theorem T-SNAP, and that the snap occurs is stated separately: it follows from the occurrence commitment '
             '(instantiation occurs) together with DA-1 (closed given DP-2). tsnap_holds_but_nothing_moves shows T-SNAP does not carry it. ✓'),
        derived('Status: DERIVED — Cross-Framework. Premises: in two readings, under Premises of T-SNAP above; the Lean form fixes the shape '
                'with no hypotheses, t_snap_given takes CC-1 and occurrence at the first step as hypotheses, and the prose argument&#8217;s shape and its '
                'occurrence rest on commitments, among them those named there. '
                'Dependencies cited in the steps: ZP-C D1, D7, L-RUN, TQ-IH; ZP-B C3; ZP-A D2, R1; ZP-E DA-1; ZP-J T-EXEC. '
                'CC-1 (S&#8320; = &#8869;): restated — a Quine-atom start and a &#8869; start are one condition (ZP-J cc1_derived, t_exec_iff; axiom-free) — and not forced, since on a carrier with a second point a valid sequence starts elsewhere. '
                'CC-2 (&#8869; = {&#8869;}): ZP-J t_exec_iff proves &#8869; is the only occupant of the Quine-atom role (axiom-free); that &#8869; is the AFA set Q = {Q} is argued metatheoretically (see R-AFA). '
                'Both remain commitments: CC-1 is a Conditional Claim, expressed through the Quine-atom role and not removed by it; CC-2 is a Forced Metatheoretic Commitment. '
                'Conceptual correspondence only: ZP-G AX-G2 (downstream of ZP-E; not a formal dependency).'),
    ]

    E += [
        sp(6),
        bridge_box(
            'Remark R-ε₀ — On the Symbol Choice for the Snap Displacement',
            [
                '<b>Note: this remark draws an informal structural analogy. No formal embedding of '
                'ZP\'s ε₀ into the ordinal ε₀ is claimed or established here.</b> '
                'The symbol ε₀ in Step 6 names an element of L strictly above ⊥ through which the Binary '
                'Snap passes; Step 6 asserts only that one exists. It is the least such element exactly '
                'where L has one: on the two-state carrier MachinePhase it is c₁, and on a linearly '
                'ordered L satisfying AX-B1 the first step is unique (axb1_gives_unique_target). AX-B1 '
                'alone does not supply a least element: on Set Bool, ∅ has two distinct first steps and '
                'no least element above it, and a dense L has no first step '
                '(axb1_fails_everywhere_iff_dense). This symbol is chosen deliberately to coincide '
                'with ε₀, the proof-theoretic ordinal of Peano Arithmetic.',
                '<b>The ordinal ε₀.</b> In ordinal arithmetic, ε₀ is the smallest fixed '
                'point of the map α → ω<sup>α</sup>: equivalently, ε₀ = sup{ω, ω<sup>ω</sup>, '
                'ω<sup>ω<sup>ω</sup></sup>, ...}. No finite ω-tower reaches it. Gentzen '
                'proved in 1936 that transfinite induction up to ε₀ is sufficient to prove Con(PA). '
                'Necessity — that no smaller ordinal would do — is the other direction, and it rests on '
                'different ground: the provability in PA of transfinite induction at every ordinal '
                'strictly below ε₀, which Gentzen reports as already known, crediting Hilbert-Bernays, '
                'together with G&#246;del\'s second incompleteness theorem, by which PA cannot prove '
                'Con(PA) from within. The '
                'ordinal ε₀ is therefore the minimum threshold at which finite arithmetic exhausts its own '
                'generative capacity.',
                '<b>The structural analogy.</b> ZP\'s ε₀ occupies an analogous position in the state '
                'lattice. At P₀, c₁ satisfies K(c₁|n)/|c₁| = 1 (ZP-C D1): it is algorithmically '
                'incompressible — no finite external program shorter than c₁ generates it. Just as the '
                'Cantor ε₀ cannot be reached from 0 by any finite ω-tower, ZP\'s ε₀ cannot be reached '
                'from ⊥ by any finite external description. Both name a structurally analogous object: the '
                'witness for a transition that exhausts the finite generative hierarchy below it.',
                '<b>The proof structures are parallel.</b> The proof-theoretic analysis locates the minimum '
                'ordinal up to which PA cannot prove transfinite induction. ZP locates the state '
                'displacement at which no external program can hold ⊥ as a static string — where unbounded '
                'surprisal (ZP-C L-INF) and self-containment (ZP-A CC-2) together eliminate any external '
                'interpreter position. In both cases the exhaustion of finite description is not a '
                'deficiency but a structural consequence: the system is necessarily executing at ε₀.',
                '<b>What is not claimed.</b> ZP does not assert that L is an ordinal structure, or that '
                'ZP\'s ε₀ is literally the Cantor ordinal under a formal embedding into the p-adic/lattice '
                'framework. The analogy is motivational: both ε₀s mark the witness for '
                'incompressibility relative to a finite base. A formal embedding — showing that the Cantor '
                'ε₀ is order-isomorphic to or embeds into the p-adic completion of L at ⊥ — remains an '
                'open question and would constitute a strengthening of this claim.',
            ]
        ),
        sp(4),
        bridge_box(
            'Remark R-AFA — Why Foundation is Ruled Out; Non-Well-Foundedness Forced, AFA Adopted',
            [
                'CC-2 &#8212; the identification of &#8869; with the Quine atom &#8869; = {&#8869;} &#8212; '
                'is a set-theoretic step beyond ZP-A\'s algebra: it is not derived from A1&#8211;A4. What it '
                'entails is nonetheless not arbitrary, and the two halves separate. The membership structure '
                'the framework\'s bottom must have <i>forces</i> a non-well-founded host, which is what rules '
                'ZF + Foundation out. <i>Which</i> non-well-founded axiom to adopt is a further step that the '
                'forcing does not take: ZF + AFA is the host this framework adopts, as the canonical theory '
                'meeting the requirements, not the one theory the bottom selects.',
                '<b>Foundation rules out the bottom (structural).</b> The framework\'s bottom is the Quine '
                'atom &#8869; = {&#8869;}: it is a member of itself, &#8869; &#8712; &#8869;. ZF + Foundation '
                '(the Axiom of Regularity) forbids exactly this — under a well-founded membership relation no '
                'set lies on a membership cycle of any length, so in particular no set is a member of itself. '
                'This is a theorem of ZF + Foundation, not a framework-specific stipulation; it is '
                'machine-checked here as no_quine_atom / no_membership_cycle '
                '(ZeroParadox/Settheory/Wall.lean, footprint [propext, Quot.sound], choice-free). A '
                'Foundation-respecting universe therefore cannot host &#8869; at all.',
                '<b>The framework\'s readings of &#8869; support the premise that &#8869; is circular; the '
                'exclusion itself is a theorem.</b> R3 '
                '(ZP-A) &#8212; &#8869; = {&#8869;} has no describer position external to itself &#8212; and '
                'L-INF (ZP-C) &#8212; the 2-adic surprisal I(n) = n is unbounded, so no finite interpreter '
                'can hold &#8869; &#8212; each describe an object with no external vantage and unbounded '
                'self-referential depth. That is exactly the profile of a non-well-founded, self-membered '
                'set: the two readings motivate why &#8869; must be the circular object Foundation excludes, '
                'rather than serving as independent proofs of the exclusion.',
                '<b>Non-well-foundedness is forced; AFA is the canonical replacement.</b> The membership '
                'structure of &#8869; = {&#8869;} is circular '
                '(&#8869; &#8712; &#8869; &#8712; &#8869; &#8712; &#8230;), so &#8869; can live only in a '
                'non-well-founded '
                'metatheory. <b>That much is forced; the particular axiom is not.</b> Aczel records four '
                'anti-foundation axioms, and AFA, FAFA and SAFA each admit exactly one '
                'Quine atom &#8212; his own term is a <i>reflexive set</i> &#8212; while being pairwise '
                'incompatible (Aczel 1988, Corollary 4.28; Appendix A, p. 108). Supplying exactly one '
                'therefore does not single AFA out, so AFA is '
                '<i>adopted</i> as the canonical witness rather than selected by the membership structure.',
                '<b>What is machine-checked (the requirements framework).</b> The question of which host '
                'theory can admit &#8869; is reduced to the two requirements a host theory must supply '
                '&#8212; <b>(Y)</b> a Quine atom &#8869; = {&#8869;} and <b>(Z)</b> its uniqueness &#8212; '
                'and largely closed in the '
                'framework\'s set-theory layer (the QuineHost development, '
                'ZeroParadox/Settheory/QuineHost.lean). Proved '
                'there: the third property, <b>(X)</b> Foundation-freeness, is not assumed &#8212; it is '
                '<i>forced</i> by (Y) (quineHost_not_wellFounded, '
                'axiom-free); ZF + Foundation is excluded (zfSet_no_quine_bottom &#8212; no set is '
                'self-membered &#8212; not axiom-free: it inherits no_quine_atom\'s footprint '
                '[propext, Quot.sound], choice-free); and the requirements are '
                '<i>realizable</i> &#8212; a concrete one-atom model exhibits them (oneAtom_not_wellFounded, '
                'axiom-free). AFA is the canonical example, exhibited off the framework\'s own '
                'AFAStructure (afaStructure_isQuineHost) &#8212; a definition rather than a theorem about '
                'the set theory, and one every ZP-A lattice supplies trivially (the NO-GO gauge in '
                'ZeroParadox/Settheory/SetTheoryAFA.lean). So the reduction '
                'to requirements is not merely argued: the forcing and the realizability are settled '
                'results. What stays argued is which requirements to demand, below.',
                '<b>Boffa is set aside on a weaker warrant, and the cited half and the checked half are '
                'separate.</b> That '
                'Boffa\'s anti-foundation axiom admits a proper class of Quine atoms rather than one is '
                'a <i>cited</i> fact about that theory, and it reaches that axiom through a weaker one, '
                'in a direction worth stating. Boffa\'s axiom is equivalent to his earlier axiom '
                'BA<sub>1</sub> '
                'together with an extension condition, so it implies BA<sub>1</sub> (Aczel 1988, Exercise '
                '5.14(i) for the equivalence; p. 59, where the axiom is formulated as Boffa\'s strengthening '
                'of BA<sub>1</sub>); and BA<sub>1</sub> on its own already '
                'forces the reflexive sets &#8212; Aczel\'s term for Quine atoms &#8212; to form a '
                'proper class (Aczel 1988, Proposition 5.1). That permissiveness is therefore '
                'inherited from the weaker axiom rather than introduced by the strengthening. This '
                'development formalizes no part of either Boffa axiom. What is machine-checked is the '
                'mechanism behind it &#8212; that '
                'self-membership alone does not force uniqueness: in a two-element toy model where every '
                'element is self-membered, no element is <i>the</i> self-membered one '
                '(boffa_fails_unique, ZeroParadox/Settheory/QuineHost.lean, axiom-free). That is a '
                'counter-model separating the two requirements, and it blocks one direction only &#8212; a '
                'host supplying the Quine atom need not supply its uniqueness. Dropping uniqueness '
                'accordingly leaves a host theory no less consistent; what it leaves standing is the '
                'Quine-atom clause alone, and in that toy model every element satisfies that clause, so '
                'the surviving clause is <i>uninformative</i> as a pinning condition &#8212; every element is a '
                'witness, and none is pinned as the host\'s distinguished bottom. Neither half is an '
                'in-kernel result about Boffa\'s axiom itself.',
                '<b>What remains &#8212; a narrow Forced Metatheoretic Commitment.</b> With the forcing and '
                'realizability proved, one step is not a theorem: that a Quine atom and its uniqueness are '
                'the <i>right</i> two requirements to demand &#8212; the commitment to &#8869; = {&#8869;} '
                'as the minimal option consistent with A4\'s additive-identity role (it has exactly one '
                'member, itself, and introduces no internal differentiation; any extension '
                '&#8869; = {&#8869;, x} with x &#8800; &#8869; would add members carrying their own '
                'membership chains). This is a <b>Forced Metatheoretic Commitment</b> &#8212; stronger than '
                'a free choice, weaker than a theorem &#8212; not a Conditional Claim; the set-membership '
                'face &#8869; &#8712; &#8869; stays metatheoretic, while the occupant of the Quine-atom role '
                'is machine-checked to be &#8869; (t_exec, ZeroParadox/Settheory/SetTheoryAFA.lean, '
                'axiom-free, given the field bot_self_mem). The named falsifier is correspondingly narrow: a differently-motivated '
                'requirement set that hosts &#8869; without demanding a unique Quine atom would reopen this '
                'choice &#8212; it would not touch the forcing or the realizability, which are settled.',
            ]
        ),
        sp(4),
    ]

    E.append(Paragraph('VI. Effect of T-SNAP on Downstream Results', S['h2']))
    E.append(body(
        'Remark R-DA1: AX-1 is retired, and its content was split in two. Results in ZP-E that '
        'previously depended on AX-1 as an axiom now depend on T-SNAP, a derived theorem, for the shape, and, wherever they use that the Snap happens, on the '
        'occurrence commitment (instantiation occurs) together with DA-1. T5 (Iterative Forcing Theorem) depended on AX-1 and is restated below. T4 (Unified Snap '
        'Description) carried AX-1 as an axiom label on the causality component — that label is upgraded '
        'to Derived — T-SNAP for the shape, with occurrence still a commitment. DA-1 is additionally upgraded from Design Principle to Derived '
        'Proposition, closed given DP-2 (da1_minimal_path); ZP-A CC-2 (⊥ = {⊥}) and R3 motivate it, with ZP-C L-INF as independent corroboration. '
        'The intentional axioms of the system are now: AX-B1 (binary existence), '
        'AX-G1 (initial object), AX-G2 (source asymmetry). AX-1 is retired: its shape is Theorem T-SNAP, and the occurrence '
        'commitment is not on this list because it is a commitment, not a named axiom. '
        'Additional structural commitments are carried as typeclass fields: A4 (bot_join, '
        'ZPSemilattice — standard semilattice algebra), AFAStructure.quine_unique and bot_self_mem '
        '(the Quine-atom role), KleeneStructure.botCode_is_quine (computational closure). Like named axioms these are '
        'assumptions, carried as hypotheses by every theorem that uses them; &#35;print axioms does not surface typeclass fields. '
        'Unlike named axioms they can be cheap to meet: every ZP-A lattice supplies AFAStructure trivially.'))
    E += [
        sp(4),
        bridge_box(
            'T5 (Iterative Forcing Theorem) — restated',
            [
                'T5 (restated). Selection. In the ordinal chart the next rung is the snap re-seeded one step past the current one '
                '(succession_succ), and none lies between two consecutive rungs (ZeroParadox/Ordinal/SnapSuccession.lean &#167; I). '
                'Carried into the two-state lattice by a monotone map that sends the tower&#8217;s stages to c<sub>0</sub> and '
                '&#949;<sub>0</sub> to c<sub>1</sub>, no ordinal below &#949;<sub>0</sub> is sent to c<sub>1</sub>, and every fixed point '
                'of &#945; &#8614; &#969;<super>&#945;</super> is (snap_unconditional, hfp_from_epsilon_zero). '
                'The two faces of &#949;<sub>0</sub> carry the two directions: as the supremum of the stages, every ordinal below '
                '&#949;<sub>0</sub> lies under one of them, so nothing below fires (fundamentalSeq_cofinal); as the least fixed point of '
                '&#945; &#8614; &#969;<super>&#945;</super> it lies below every other, so every fixed point of &#945; &#8614; &#969;<super>&#945;</super> fires '
                '(hfp_from_epsilon_zero, epsilon0_min_eq_max). The placement at &#949;<sub>0</sub> is a hypothesis there '
                '(h&#949;<sub>0</sub>), which the Lean names the alignment hypothesis; deriving it from the 2-adic structure is open, as the Classical.choice '
                'inversion conjecture (ZeroParadox/Ordinal/Incompleteness.lean). The rungs are the iterative bottoms; '
                'none of them is &#8869; (epsilon0_ne_bot; for every rung, Ordinal.epsilon_pos). On an arbitrary lattice no step is '
                'selected: 0, 2, 4, &#8230; on the natural numbers satisfies A1&#8211;A4 and AX-B1.',
                'Iteration. No step is guaranteed. A state sequence moves only upward (T3) and never returns (R1, t_snap_irreversible). '
                'Where the next increment is already absorbed (S<sub>n</sub> &#8744; &#945;<sub>n</sub> = S<sub>n</sub>), the state stays '
                'the same, which T-SNAP permits (tsnap_holds_but_nothing_moves); different runs need not reach the same height. If from '
                'some step x on every new increment is already absorbed, then S<sub>x</sub> is the supremum of the run: the value that run '
                'reaches in the limit. Short of a top, reaching it cannot be confirmed at any finite step; a run that reaches a top state '
                '(c<sub>1</sub> on the two-state carrier) is known there to stay.',
                'Reading: &#949;<sub>0</sub> is both at once for the ordinal tower: the least fixed point of &#945; &#8614; '
                '&#969;<super>&#945;</super> and the supremum of its stages (epsilon0_min_eq_max).',
                'The handle T5 is kept. &#8220;Forcing&#8221; names the shape of each step taken, not that any step is taken.',
            ]
        ),
    ]

    print('[build_zpe] Building DA-2...')
    # ── FORMAL INSERT DA-2 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-2: Instantiation Succession — The Multiple-&#8869; Result', S['h1']),
        Paragraph('<i>Formally licenses the directed instantiation tree</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-2 Closes', S['h2']))
    E.append(body('Given the premises stated under Premises of T-SNAP (DA-1 insert, &#167; V), DA-1 and T-SNAP give the Binary Snap on reaching P<sub>0</sub> '
                  'within an instantiation. Three questions remain open after DA-1:'))
    E += [
        li('CC-1 (ZP-A) posits S<sub>0</sub> = ⊥ — not derivable from A1–A4 alone (ZP-J restates it as '
           'an equivalence with starting at a Quine atom, cc1_derived and t_exec_iff, and does not force it). This leaves open whether ⊥ is unique across all instantiations or whether '
           'each instantiation carries its own ⊥.'),
        li('ZP-B R1 distinguishes universal structure from universe-contingent parameters. ε<sub>0</sub> is '
           'contingent per instantiation. Whether ⊥ is similarly contingent is not addressed in ZP-A through ZP-D.'),
        li('<b>Occurrence fence.</b> T-SNAP fixes the SHAPE of each step. It does not establish that any step is taken: tsnap_holds_but_nothing_moves exhibits a model in which T-SNAP holds and nothing moves. Every "fires" below narrates the commitment that instantiation occurs, not a consequence of the theorem.'),
        li('T-SNAP fires wherever P<sub>0</sub> conditions are met. If the terminal state of instantiation I<sub>n</sub> '
           'satisfies P<sub>0</sub> conditions, T-SNAP should apply — but this requires formally connecting that '
           'terminal state to a ⊥ role-occupant, read as a new ⊥ under C-DA2. DA-2 provides this connection.'),
        sp(4),
    ]

    E.append(Paragraph('II. Why ZP-B C3 is Not Violated', S['h2']))
    E += [
        body('C3 prohibits a continuous path from x ≠ 0 back to the same 0 in Q<sub>2</sub>. DA-2 does not require a '
             'return path. The irreversibility of C3 is preserved within each instantiation. What crosses the '
             'instantiation boundary is not a path in Q<sub>2</sub> — it is the generation of a new Q<sub>2</sub> with its own '
             'metric, its own ⊥, its own ε<sub>0</sub>. C3 quantifies only over paths within a single topological space '
             'and has nothing to say about the boundary between spaces.'),
        body('More precisely: C3 rules out a continuous return to 0 WITHIN one Q<sub>2</sub>. It does not '
             'follow that a recurrence of ⊥ must be a structurally distinct ⊥ — that step needs the '
             'separateness of the spaces, which is a modelling commitment (C-DA2) and not something the '
             'topology supplies. The topology does not enforce novelty; it is silent on it, and in the '
             '2-adic chart the arc reapproaches the same 0 (snap_arc_z2_loop).'),
    ]

    E.append(Paragraph('III. Definitional Alignment DA-2 — Instantiation Succession', S['h2']))
    E.append(bridge_box(
        'Definitional Alignment DA-2 — Instantiation Succession',
        [
            'Claim: A state S in instantiation I<sub>n</sub> satisfies the structural role of ⊥ for instantiation '
            'I<sub>n+1</sub> if and only if it satisfies A4 relative to all subsequent joins in I<sub>n+1</sub>:',
            'S ∨ x = x    for all x in the semilattice of I<sub>n+1</sub>.',
        ]
    ))
    E += [
        sp(4),
        body('Grounding: A4 is the load-bearing axiom of ZP-A — it defines ⊥ as the additive identity under '
             '∨, the element that contributes nothing to any join and is therefore present in everything '
             'above it. DA-2 does not redefine ⊥. It clarifies that the CC-1 identity condition (S<sub>0</sub> = ⊥) can be '
             'satisfied by any state meeting A4\'s algebraic conditions — not only by a cosmologically '
             'primitive ⊥. The identity condition is structural, not historical: what matters is the '
             'algebraic role a state plays in the subsequent semilattice, not where it came from.'),
        body('The terminal state of I<sub>n</sub> arrives at I<sub>n+1</sub> carrying the accumulated join of everything in I<sub>n</sub>\'s '
             'sequence. It is structurally ⊥ to I<sub>n+1</sub> — contributing nothing to subsequent joins — while '
             'being informationally rich relative to I<sub>n</sub>. This is the Zero Paradox instantiated at the '
             'inter-instantiation level: the terminal state is simultaneously a terminus and a foundation.'),
        derived('Status: DEFINITIONAL ALIGNMENT — no new axiom introduced. DA-2 is a clarification of '
                'the scope of CC-1 and A4. ✓'),
    ]

    E.append(Paragraph('IV. Conditional Claim C-DA2 — Novelty of Successive ⊥', S['h2']))
    E.append(bridge_box(
        'Conditional Claim C-DA2 — Novelty of Successive ⊥ (a modelling commitment)',
        [
            'Commitment: each instantiation carries its OWN topological space, so the ⊥ of '
            'I<sub>n+1</sub> is not an element of the Q<sub>2</sub> of I<sub>n</sub>. GIVEN that, no two '
            'instantiations share a ⊥, and succession is a chain (or tree) rather than a cycle.',
            'Status: CONDITIONAL, not derived. The commitment above is the separateness of the '
            'spaces; it is assumed, not obtained from C3. Formerly labelled a Corollary and marked '
            'derived — retracted, see the note below. The handle C-DA2 is unchanged.',
            'What IS proved: that anything occupying the bottom role IS the bottom of its own '
            'lattice (t_iz_limit_is_new_null). That is an identity with the bottom already '
            'present, not the production of a second one.',
        ]
    ))
    E += [
        sp(4),
        body('Why this is NOT a proof, stated plainly because it was published as one. The step '
             '"the ⊥ of I<sub>n+1</sub> is an element of a distinct topological space" is the CONCLUSION, '
             'not a consequence of C3. C3 quantifies over paths WITHIN a single space — it says no continuous '
             'path runs from any x ≠ 0 back to 0 inside one Q<sub>2</sub> — and has nothing to say about '
             'whether the next instantiation\'s space is a different one. Assuming separateness and then '
             'deriving distinctness from it is circular. DA-2 likewise fixes identity conditions WITHIN an '
             'instantiation; it does not compare across two.'),
        body('And the corpus measures against it where the question is concrete: in the 2-adic realization '
             'the arc returns to the SAME zero. snap_arc_z2_loop proves the tower starts at 0, that every '
             'finite stage is ≠ 0, and that it converges back to 0; tower_image_loops_to_seed states the '
             'limit IS the seed value. So in that chart novelty does not merely lack a proof — it fails. '
             'C-DA2 stands as a modelling commitment about instantiations, and must not be cited as derived, '
             'nor supported by T-IZ or by t_iz_limit_is_new_null.'),
    ]

    E.append(Paragraph('V. The Directed Instantiation Tree', S['h2']))
    E.append(body('With DA-2 and C-DA2 in place, the global structure of instantiations is a forward-directed '
                  'tree with no back edges:'))
    E += [
        li('Each node in the tree is a ⊥ — the bottom element of one instantiation and the foundation of all '
           'successor instantiations branching from it.'),
        li('Each edge within an instantiation is a step in a monotone state sequence (ZP-A T3). Edges are irreversible (ZP-B C3).'),
        li('Branching at each node: every distinct outbound vector from the terminal state of I<sub>n</sub> is a '
           'valid ε<sub>0</sub> for a distinct I<sub>n+1</sub>. T-SNAP does not select among branches. Because ⊥ = {⊥} '
           '(ZP-A CC-2) is the single self-containing ⊥ with no internal differentiation, every '
           'ε<sub>0</sub> that represents a first differentiation in any direction is a valid outcome. '
           'The work here is done by the undifferentiated ⊥ of CC-2, not by T-SNAP: given that '
           'instantiation occurs, no direction is privileged, so the structure branches rather than '
           'threading a line. T-SNAP fixes the shape of each step; it does not supply the occurrence.'),
        li('No back edges: C-DA2 COMMITS to no instantiation reaching the ⊥ of any ancestor. This is the commitment, not a theorem - in the 2-adic chart the arc returns to the same 0 (snap_arc_z2_loop).'),
        sp(4),
    ]
    E.append(body(
        'Remark R-DA2: T-SNAP fires wherever P<sub>0</sub> conditions are met. DA-2 establishes that the terminal '
        'state of I<sub>n</sub> satisfies those conditions for I<sub>n+1</sub>. T-SNAP therefore applies across instantiation '
        'boundaries without modification. No new axiom is required. The multiverse is not the claim that '
        'T-SNAP fires in all directions simultaneously: it is the claim that ⊥ = {⊥} (ZP-A CC-2) has no '
        'internal differentiation and therefore no preferred direction for ε<sub>0</sub>. The multiverse of '
        'instantiations is the full set of all minimal differentiations available from the single '
        'self-containing ⊥ — a structural consequence of CC-2 + T-SNAP + DA-2 jointly.'))


    E.append(Paragraph('VI. The Zero Paradox Iterated', S['h2']))
    E.append(body('The paradox of ⊥ — simultaneously contributing nothing and being present in everything — '
                  'propagates structurally at every branching node of the tree. Each node is:'))
    E += [
        li('Nothing to its successor instantiations: it acts as additive identity under ∨, contributing nothing to any subsequent join.'),
        li('Everything to its successor instantiations: every state in I<sub>n+1</sub> satisfies ⊥<sub>n+1</sub> ≤ S, so the node underlies everything that follows.'),
        sp(4),
    ]
    E += [
        body('The tree is the geometric shape of the Zero Paradox iterated across instantiations. The '
             'single-instantiation linear sequence was always a cross-section of a structure with this shape.'),
        body('The complete picture: The Zero Paradox describes a forward-directed infinite tree where '
             '⊥<sub>1</sub> → ... → S<sub>terminal</sub><sup>1</sup> ≡ ⊥<sub>2</sub> → ..., where ≡ means structurally satisfies the role of, '
             'not is identical to. Each arrow within an instantiation is monotone and irreversible. Each ≡ '
             'crossing is not a path — it is a new instantiation of the universal structure.'),
    ]

    E.append(Paragraph('VII. Implications Within the Framework', S['h2']))
    E += [
        body('<b>Structural Implication: Branching Tree Structure.</b> T-SNAP fixes the SHAPE of the Binary Snap — '
             'that if ⊥ transitions it goes to some ε₀ > ⊥, and that the step is one-way. It does not '
             'establish that the transition is taken: that the Snap occurs follows from the occurrence commitment (instantiation occurs) '
             'together with DA-1 (closed given DP-2), and the NO-GO '
             'gauge tsnap_holds_but_nothing_moves exhibits a model in which T-SNAP holds and nothing moves. '
             'DA-2 establishes that any terminal state satisfying P₀ '
             'conditions acts as ⊥ for a successor instantiation, generating a forward-directed branching '
             'tree. The branching comes from CC-2\'s undifferentiated ⊥ and the succession from DA-2, '
             'both conditional on instantiation occurring. Note: T-SNAP alone does '
             'not establish that it fires on all outbound vectors simultaneously — that universality is the '
             'scope of DA-2, not a direct consequence of the snap theorem itself.'),
        body('<b>Monotonicity and Path Irrecoverability.</b> Within an instantiation, state sequences are monotone — no state '
             'can be decreased (ZP-A R1). Every state change is a join operation: S<sub>n</sub> ∨ α for some increment α. '
             'The algebra constrains only that the sequence be monotone, not which monotone path is '
             'taken. Each join adds informational content irreversibly. States are permanently '
             'encoded in the element\'s position in L.'),
        body('<b>Ordinal Direction of State Sequences.</b> The monotone sequence (ZP-A T3) is a structural definition of '
             'directional asymmetry in state ordering. Irreversibility is C3 applied within an instantiation. The framework does not '
             'assume directional asymmetry — it derives it.'),
        body('<b>Causal structure.</b> Every state is fully determined by the joins that produced it. The causal '
             'history of any state is encoded in its position in L. No effect without the join that produced it.'),
    ]

    print('[build_zpe] Building DA-3...')
    # ── FORMAL INSERT DA-3 ────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Formal Insert DA-3: Perspective-Relative Cardinality', S['h1']),
        Paragraph('<i>Cardinality as position-dependent measurement within the instantiation structure</i>', S['note']),
        hr(),
    ]

    E.append(Paragraph('I. The Gap DA-3 Closes', S['h2']))
    E.append(body(
        'DA-2 establishes that instantiations form a directed tree and that branching at each ⊥ node '
        'produces multiple successor instantiations. This raises a question about the cardinality of '
        'branching: is the fan at each node countably or uncountably infinite? The answer, which DA-3 '
        'formalises, is that this question is perspective-dependent — and DA-3 further conjectures '
        '(Claim DA-3-C1, deferred to OQ-E2) that this perspective-dependence is the same structural feature '
        'underlying the major cardinality anomalies of classical set theory.'))

    E.append(Paragraph('II. Perspective-Dependence of Branching Cardinality', S['h2']))
    E.append(body(
        'From within instantiation I<sub>n</sub>, an observer occupies exactly one branch of I<sub>n+1</sub>. The other '
        'branches of I<sub>n+1</sub> are not accessible via any path — C3 and monotonicity jointly prohibit it. '
        'From inside, the branching factor is always 1: the observer sees one branch. From outside — '
        'from a meta-level view of the tree — the branching factor is the full fan of accessible outbound vectors.'))
    E.append(bridge_box(
        'Definition DA-3-D1 — Accessible Cardinality',
        [
            'The accessible cardinality of a position p in semilattice L is the cardinality of the set of '
            'states reachable from p by monotone sequences within the instantiation containing p.',
        ]
    ))
    E += [
        sp(4),
        body('The accessible cardinality from p is determined entirely by the structure of L above p. It is not '
             'an intrinsic property of a collection — it is a property of the relationship between a position '
             'and the states reachable from it. No position within any instantiation can access all '
             'cardinalities simultaneously. The meta-level view, which sees the full branching fan, is not a '
             'position any element of any instantiation can occupy.'),
        body('Remark R-DA3-1: To observe the full branching fan, one would need to occupy a position '
             'outside all instantiations. That position would itself be a state in some semilattice, subject to '
             'the same rules. The meta-view is either another instantiation (in which case the tree has no '
             'privileged outside view) or ⊥ itself (in which case ⊥ is the only position from which '
             'the full structure is visible — the state that contributes nothing and is present in everything). '
             'The Zero Paradox\'s name is more precise than it first appeared.'),
    ]

    E.append(Paragraph('III. The Cardinality Hierarchy as Perspective-Relative', S['h2']))
    E.append(body(
        'Cantor\'s theorem establishes that for any set S, |P(S)| > |S|, generating the hierarchy '
        'ℵ<sub>0</sub> &lt; 2<sup>ℵ<sub>0</sub></sup> &lt; 2<sup>2<sup>ℵ<sub>0</sub></sup></sup> &lt; ... '
        'DA-3 reframes this hierarchy not as a fixed ladder that mathematics climbs, but as a '
        'perspective-relative description of the branching structure of the instantiation tree, as seen '
        'from within different positions.'))
    E.append(bridge_box(
        'Claim DA-3-C1 — Perspective-Relative Absolute Cardinality',
        [
            'The appearance of absolute cardinality — cardinality as an intrinsic property independent of '
            'measuring position — is an artifact of treating the semilattice as having a view from outside. '
            'DA-2 and C-DA2 jointly prohibit such a view from within any instantiation.',
        ]
    ))
    E += [
        sp(4),
        body('The candidate claim (DA-3-C1) is that accessible cardinality from within any instantiation '
             'cannot replicate the view from outside. Whether specific independence results in classical '
             'set theory are formal expressions of this perspective-dependence is the conjecture that '
             'OQ-E2 is tasked with investigating.'),
        derived('Status: DEFINITIONAL ALIGNMENT + CANDIDATE CLAIM. DA-3-D1 and R-DA3-1 are '
                'definitional. DA-3-C1 is a candidate claim: structurally motivated within the framework; '
                'formal derivation of the connection between accessible cardinality and specific '
                'set-theoretic independence results is deferred to OQ-E2.'),
    ]

    print('[build_zpe] Building registers...')
    # ── UPDATED OPEN ITEMS REGISTER ───────────────────────────────────────────
    E += [hr(), Paragraph('Updated Open Items Register', S['h1'])]

    oq_rows = [
        ['AX-1: Binary Snap Causality',
         'RETIRED — shape proved as T-SNAP; the snap occurs given the occurrence commitment and DA-1',
         'Its content was split in two: the shape of the Snap is proved, as Theorem T-SNAP (from L-RUN, TQ-IH and the bottom law, with no Lean kernel axioms), '
         'and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
         'Premises under Premises of T-SNAP (DA-1 insert, &#167; V); given CC-1, the first-step form of the Snap occurring is the hypothesis hocc of t_snap_given.'],
        ['DA-1: Derived Proposition (DP-2 formal grounding)',
         'CLOSED — DP-2 (formal core); CC-2 + L-INF + AIT (corroboration of precondition)',
         'Primary formal grounding: DP-2 (TrackedOutput, Snap.lean &#167;VI) — da1_minimal_path proved '
         'axiom-free. Instantiation of &#8869; moves machine from c<sub>0</sub> to c<sub>1</sub>; output value is irrelevant '
         'to whether execution occurred. '
         'Informal corroboration: ZP-A CC-2 + R3 (structural); ZP-C L-INF (informational); AIT incompressibility (Path 3).'],
        ['DA-2: Instantiation Succession',
         'CLOSED — Definitional',
         'Terminal state of I<sub>n</sub> satisfies A4 role of ⊥ for I<sub>n+1</sub>. C-DA2 COMMITS to the novelty of each ⊥; it does not establish it.'],
        ['DA-3: Perspective-Relative Cardinality',
         'CLOSED (definitional) / CANDIDATE (DA-3-C1)',
         'DA-3-D1 establishes accessible cardinality is position-dependent within the instantiation structure. '
         'DA-3-C1 (candidate): no position within an instantiation can replicate the outside view. '
         'Whether this connects formally to specific set-theoretic independence results is deferred to OQ-E2.'],
        ['OQ-A1: Increment selection',
         'OQ-A1b CLOSED by A1&#8211;A4; OQ-A1a: no reason to restrict to join-irreducibles (well-founded carriers); placement in the ordinal tower, for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, conditional on the alignment hypothesis h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>)',
         'T5 (Iterative Forcing Theorem), restated in DA-1 insert &#167; VI. No step is guaranteed. On an arbitrary lattice no step is '
         'selected: 0, 2, 4, &#8230; on the natural numbers satisfies A1&#8211;A4 and AX-B1.'],
        ['OQ-B1: p = 2',
         'CLOSED — ZP-B T0',
         'Derived from AX-B1 and MP-1.'],
        ['OQ-C1: Non-conservatism of DF',
         'CLOSED — ZP-C T2',
         'Infinite sequence divergence proven. No postulates remain.'],
        ['S1: Distribution stipulation',
         'CLOSED — ZP-C T1',
         'Derived from AX-B1 and RP-1.'],
        ['OQ-E1: Sequence vs. tree',
         'CLOSED given the occurrence commitment — DA-2',
         'The structure is a forward-directed tree, not a linear sequence. Given that instantiation occurs — the '
         'occurrence commitment, not a consequence of T-SNAP — DA-2 supplies the succession and the '
         'branching follows. '
         'Countable vs. uncountable branching is perspective-dependent (DA-3).'],
        ['OQ-E2: Cardinality-semilattice correspondence',
         'OPEN',
         'Do specific semilattice structures correspond to specific cardinality regimes? Can the framework '
         'make predictions about which instantiations satisfy CH and which do not?'],
        ['Remaining axioms',
         'INTENTIONAL — AX-B1, AX-G1, AX-G2 (named); A4, quine_unique, bot_self_mem, botCode_is_quine (typeclass fields)',
         'Named commitments: AX-B1 (binary existence), AX-G1 (initial object), AX-G2 (source asymmetry). '
         'Structural commitments as typeclass fields: A4/bot_join (ZPSemilattice), '
         'AFAStructure.quine_unique and bot_self_mem (the Quine-atom role, which every ZP-A lattice supplies trivially), '
         'KleeneStructure.botCode_is_quine (computational closure). '
         'Typeclass fields are assumptions carried as hypotheses by the theorems that use them; &#35;print axioms does not surface them. Further commitments are not axioms, among them CC-1 (S<sub>0</sub> = &#8869;), a ZP-A Conditional Claim; T-SNAP&#8217;s are stated under Premises of T-SNAP (DA-1 insert, &#167; V).'],
        ['Temperature T in BA-1',
         'PARAMETER — intentional',
         'Universe-contingent. Physical predictions explicitly conditional on instantiation-specific T.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.20, TW*0.58]
    ))

    # ── UPDATED TRACEABILITY REGISTER ─────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Updated Traceability Register', S['h1'])]

    trace_rows = [
        ['Binary Snap causality',
         'Shape: ZP-C D1, L-RUN, TQ-IH; ZP-A D2; T-SNAP premises: DA-1 insert &#167; V. Occurrence: the occurrence commitment and DA-1',
         'None',
         'Derived for the shape — T-SNAP ✓; the snap occurs given the occurrence commitment and DA-1 (was: Axiomatic — AX-1)'],
        ['DA-1: Instantiation = execution',
         'DP-2 (TrackedOutput, Snap.lean &#167;VI); ZP-A CC-2, R3; ZP-C L-INF',
         'None',
         'Derived Proposition — primary: DP-2 (da1_minimal_path proved axiom-free in Lean). '
         'Informal paths: CC-2/R3 (structural), L-INF (informational), AIT incompressibility (Path 3). '
         'AIT+ZF+AFA outside Lean scope.'],
        ['DA-2: Instantiation succession',
         'ZP-A A4, CC-1; ZP-B C3, R1; T-SNAP',
         'None',
         'Definitional Alignment — clarification of CC-1 scope; no new axiom'],
        ['C-DA2: Novelty of ⊥ (conditional)',
         'DA-2, ZP-B C3',
         'None',
         'CONDITIONAL — a modelling commitment. NOT derived: the separateness of the spaces is assumed, not obtained from C3, and snap_arc_z2_loop returns to the same 0.'],
        ['DA-3: Perspective-relative cardinality',
         'DA-2, C-DA2, ZP-B R1',
         'None',
         'Definitional (DA-3-D1, R-DA3-1); Candidate (DA-3-C1: outside-view inaccessibility)'],
        ['T-SNAP: Snap shape is derived',
         'L-RUN, TQ-IH (the T-BUF chain&#8217;s lemmas); T-SNAP premises: DA-1 insert &#167; V. DA-1 bears on occurrence, not on the shape',
         'None',
         'Derived — Cross-Framework ✓'],
        ['AX-1 retirement',
         'T-SNAP proves the shape; the snap occurs given the occurrence commitment and DA-1',
         'N/A',
         'AX-1 is retired: T-SNAP proves the shape, and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2)'],
        ['Iterative Forcing T5 (restated)',
         'Selection: succession_succ, ZeroParadox/Ordinal/SnapSuccession.lean &#167; I; for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, given the alignment hypothesis h&#949;<sub>0</sub>, nothing below &#949;<sub>0</sub> fires (snap_unconditional). Iteration: T3, R1, t_snap_irreversible, tsnap_holds_but_nothing_moves',
         'None',
         'On an arbitrary lattice no step is selected. No step is guaranteed.'],
        ['Multiverse — structural implication',
         'T-SNAP + DA-2 jointly',
         'None',
         'Structural implication given the occurrence commitment — T-SNAP gives the snap\'s shape, CC-2\'s undifferentiated ⊥ the branching, DA-2 the succession'],
        ['OQ-E2: Cardinality correspondence',
         'DA-3',
         'N/A',
         'OPEN — formal derivation deferred'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.22, TW*0.28, TW*0.12, TW*0.38]
    ))

    # ── VALIDATION STATUS ─────────────────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Validation Status', S['h1'])]

    val_rows = [
        ['DA-1: Derived Proposition (Path 2 recharacterization)',
         'Valid — DP-2 formal core: da1_minimal_path proved axiom-free in Lean (Snap.lean &#167;VI). '
         'TrackedOutput separates output value from machine state; pre- and post-instantiation states '
         'are provably distinct even when both produce &#8869;. ✓ '
         'ZP-K: da1_closed_concrete : IsQuineAtom(&#8869; : MachinePhase) proved in Kleene.lean. '
         'Path 1 is witnessed by da1_closed_concrete, which proves nothing computational; Path 3&#8217;s witness is the '
         'machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure requirement, not a second independent proof. '
         'da1_paths_unified carries the two together as a conjunction of witnesses; that they name one structural fact is the framework&#8217;s reading. '
         'Path 2 (informational bridge, L-INF): FOUNDATIONAL COMMITMENT — a missing principle, not a '
         'missing proof. No computability library closes the gap between \'system at P₀\' and \'system is '
         'running.\' Forward paths: new axiom, Chalmers\' implementation notion, or '
         'The Philosophical Question That Started This. ZP-M R-M.1 provides a retrospective structural analysis of why the gap resisted formalization. '
         'DA-1 does not depend on Path 2. '
         'CC-1 restated in ZP-J as an equivalence, and not forced (a valid sequence can start elsewhere on a carrier with a second point); CC-2 a Forced Metatheoretic Commitment whose Quine-atom role t_exec_iff shows only &#8869; fills.'],
        ['T-SNAP: Binary Snap derived',
         'Valid — Derived, in two readings. The Lean form (t_snap_derived) fixes the SHAPE with no hypotheses and no axioms. '
         'The seven-step prose argument uses commitments, and that the transition OCCURS is not established by T-SNAP (tsnap_holds_but_nothing_moves). '
         'Premises: DA-1 insert &#167; V, Premises of T-SNAP; two of them (CC-1 and occurrence at the first step) as hypotheses, t_snap_given. ✓'],
        ['AX-1 retirement',
         'Valid — AX-1 is retired, and its content was split in two. T-SNAP proves the shape, '
         'strengthened from assumed to derived. That the Snap occurs is stated separately: it follows from the occurrence commitment '
         '(instantiation occurs) together with DA-1 (closed given DP-2). Given CC-1, its first-step form is the hypothesis hocc in t_snap_given; '
         'tsnap_holds_but_nothing_moves shows T-SNAP does not carry it.'],
        ['DA-2: Instantiation Succession',
         'Valid — Definitional Alignment. Clarification of CC-1 scope. No new axiom. A4 role of ⊥ extended across instantiation boundaries. ✓'],
        ['C-DA2: Novelty of ⊥ (conditional commitment)',
         'CONDITIONAL — a modelling commitment. NOT derived: the separateness of the spaces is '
         'assumed, not obtained from C3, which quantifies only over paths WITHIN one space. '
         'snap_arc_z2_loop measures against it — the 2-adic arc returns to the same 0. Must not '
         'be cited as derived.'],
        ['Directed instantiation tree',
         'Valid given the occurrence commitment — structural consequence of T-SNAP + DA-2. Once instantiation is taken to occur, branching follows and is not optional. Forward edges only.'],
        ['Branching tree structure',
         'Valid given the occurrence commitment — T-SNAP + DA-2 jointly. T-SNAP fixes the snap’s SHAPE and does NOT establish that it occurs; DA-2 establishes the branching tree structure. Universality (all outbound vectors) is DA-2\'s scope, not T-SNAP alone.'],
        ['Monotonicity and path irrecoverability',
         'Valid — Structural consequence. Monotonicity (T3) constrains direction; additive ontology (R1) prohibits reduction. Path choice is undetermined by algebra.'],
        ['Ordinal direction of state sequences',
         'Valid — Derived from ZP-A T3 (monotonicity) and ZP-B C3 (irreversibility). Not assumed.'],
        ['DA-3: Perspective-Relative Cardinality',
         'Valid (definitional components: DA-3-D1, R-DA3-1). Candidate (DA-3-C1: connection to specific set-theoretic independence results). OQ-E2 open.'],
        ['DA-3-C1 — outside-view inaccessibility',
         'Candidate — no position within any instantiation can replicate the meta-level view of the branching structure. Formal derivation deferred to OQ-E2.'],
        ['Remaining axioms: AX-B1, AX-G1, AX-G2; typeclass fields A4, quine_unique, bot_self_mem, botCode_is_quine',
         'Named: AX-B1, AX-G1, AX-G2. Typeclass: A4/bot_join (ZPSemilattice), '
         'quine_unique + bot_self_mem (AFAStructure), botCode_is_quine (KleeneStructure). '
         'Assumptions carried as hypotheses by the theorems that use them; not surfaced by &#35;print axioms. CC-1 is a further commitment (ZP-A Conditional Claim).'],
        ['ZP-E results T1–T4, T6, T7',
         'Stated in an earlier version of this document (see the repository history) and not restated here. T5 is restated in DA-1 insert &#167; VI.'],
    ]
    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.32, TW*0.68]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>ZP-E carries three formal inserts (DA-1, DA-2, DA-3). T-SNAP is derived, with its premises stated in the DA-1 insert &#167; V and two of them (CC-1 and occurrence at the first step) as the hypotheses of t_snap_given; its irreversibility '
            'rests on ZP-A R1 and ZP-B C3, with ZP-G downstream. DA-1 is closed given DP-2 (da1_minimal_path, axiom-free). '
            'Path 1 is witnessed by da1_closed_concrete (ZP-K), which proves IsQuineAtom(&#8869; : MachinePhase) and nothing '
            'computational; Path 3&#8217;s witness is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure '
            'requirement, not a second independent proof; and '
            'Path 2 is a foundational commitment (a missing principle, not a missing proof). Remark '
            'R-&#949;<sub>0</sub> justifies the &#949;<sub>0</sub> symbol as a structural analogy. Remark '
            'R-AFA rules Foundation out by the self-membership of &#8869; = {&#8869;} (Regularity, '
            'no_quine_atom): the forcing and realizability of the AFA requirements are machine-checked '
            '(QuineHost), and a narrow Forced Metatheoretic Commitment remains. Open question: OQ-E2. '
            'Remaining axioms: AX-B1, AX-G1, AX-G2.</i>',
            S['endnote']),
    ]

    print(f'[build_zpe] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpe] Written: {out_path}')


if __name__ == '__main__':
    build()
