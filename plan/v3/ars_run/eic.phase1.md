## Contract Paraphrase

D1 (methodology_rigor, mandatory, owned by the methodology seat): from an editorial standpoint, the planned study design must be capable of producing evidence an ITP programme committee would accept, with defined measures, sample sizes, controls, data handling and a credible reproducibility path (artifact, versions, build instructions). Because the submission is a plan, this dimension asks whether execution as described would meet that bar, not whether statistics already exist.

D2 (domain_accuracy, mandatory, owned by the domain seat): the plan's statements about the relevant proof assistants, verified-compiler engineering, prior migration and proof-translation efforts, and LLM-assisted proving must match the current state of the field, with prior work represented fairly and terminology used correctly.

D3 (argumentative_coherence, mandatory, owned by the devil's advocate with methodology also eligible): the central thesis of the planned paper must hang together, with each intended claim matched by evidence the design can actually generate, and no reasoning gap or overreach that would undermine the main argument.

D4 (cross_disciplinary_relevance, high priority, owned by the perspective seat): framing and definitions should be accessible to readers from adjacent communities, such as machine-learning evaluation researchers reading an ITP paper and vice versa, and any interdisciplinary claim must be substantiated rather than asserted.

D5 (writing_and_structure, normal priority, owned by me): the plan itself must be clearly organised and readable, and the paper it describes must be realistically deliverable within venue conventions, here a 16-page LIPIcs regular paper under lightweight double-blind review, including sensible allocation of space, figure and table plans, and anonymisation.

D6 (venue_fit_and_contribution, mandatory, owned by me): the planned paper must belong at the configured ITP venue and offer an original, significant contribution to its readership, meaning a result or lesson that proof engineers and ITP researchers would value beyond a project report, clearly distinguished from what is already known.

## Scoring Plan

### D5: writing_and_structure
dimension_id: D5
what_to_look_for: A plan whose sections, research questions, and intended outputs are easy to follow, plus a credible outline showing the planned paper fits 16 LIPIcs pages with appendices or artifact for overflow, and attention to double-blind anonymisation.
what_triggers_block: The planned paper evidently cannot fit the page limit without dropping core content, or the plan is organised so poorly that its research questions and deliverables cannot be identified.
what_triggers_warn: Exposition is uneven, terminology drifts, the space budget or figure and table plan is vague, or anonymisation of a well-known project is not addressed.

### D6: venue_fit_and_contribution
dimension_id: D6
what_to_look_for: A clearly stated contribution that ITP readers would value, such as reusable proof-engineering lessons, migration methodology, or a rigorous evaluation of AI assistance, positioned against prior work and scoped to what one regular paper can deliver.
what_triggers_block: The claimed contribution is not clearly distinguishable from existing work or is framed mainly as a progress report, so significance to the ITP community is not established without substantial reframing.
what_triggers_warn: The contribution is real but under-argued, over-broad for one paper, or split between competing framings that dilute its significance to ITP readers.
what_triggers_fatal: The planned paper lies outside the scope of ITP altogether or offers no original contribution that the venue's readership could use, even if executed perfectly.
criteria_binding_unavailable

[CONTRACT-ACKNOWLEDGED]
