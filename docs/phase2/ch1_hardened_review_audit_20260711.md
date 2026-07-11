# Chapter 1 hardened semantic review audit

Final audit date: 2026-07-11. Branch: `codex/ch1-kenneth-fin-431-clean`.
Kenneth upstream: `2b86c183a7da2bd1af77a99870b93197067d7558` (tree `95da03e39418ce2435f4f161a36d663411f5e87b`).

## Result

All 23 requested tasks have `phase2_status=pass` on the current hardened review basis. There are no allowed exceptions, hidden legacy/audit items, or deferred source-statement risks. Both historical exception boundaries were eliminated by authoritative source errata plus fresh independent review.

## Evidence

- Hardened harness commits: `2070370`, `4940203`, `6e1c95f`.
- Kenneth integration commit: `a724fa8`; source repair commit: `e7ba546`.
- Fresh final batch-plan: `all_clean_or_allowed_exception=true`, 23 rows pass, zero hidden/deferred items.
- Chapter 1 build: 49 matching task/support modules (superset of the expected 40) built successfully, ending at 8611/8611 jobs.
- Python review/freshness/batch suite: 187 passed, 9 subtests passed, 1 known runpy warning.
- Forbidden scan: zero `sorry`, `admit`, explicit `axiom`, and `native_decide`.
- Axiom audit: every one of the 23 public declarations depends on at most `propext`, `Classical.choice`, and `Quot.sound`.
- Repository hygiene command still reports pre-existing tracked Chapter 9–14 `output_lean_files`; this campaign added none and did not delete unrelated protected history.

## Per-task review/apply receipts

All hashes below are the ledger's latest applied receipt fields after `review-apply`.

| task | status | proof class | subject | basis | input | result | artifact |
|---|---|---|---|---|---|---|---|
| def_1_1 | pass | textbook_definition_completed | 4675fc2596262f971173f7b51eab1c4d04186cfa73be5f2bec2f77d838bb03b3 | eaa138f8964ab6f8c2442d722060a5352c2a8ead2cc047c70a03eb97ddde4b78 | b33257e0a030f87174886f770aacfe8c9485e096c15127e5a6e9c2803bea71aa | d171614b3e105568228332073ef07d2ff2057a8e0f0a96bb35fa7724709aef2f | semantic_review_result_v7.json |
| def_1_2 | pass | textbook_definition_completed | 0f0d305f8a2fafb3fa7b9835cbd24b349af47ac3e210bcef455f68398fe298df | 178ea094cf48f5a490b5a83924914a22506c112cedd515ba73acff406c9e01df | 0cb8f2736a4b89963488c33fc9ec80820bd4444e5128398099e4326dc34b3383 | 35a33cc299cb411e0a524d42026ebd8b6efe511c2b59031cb01fa98ace543a94 | semantic_review_result_v15.json |
| def_1_3 | pass | textbook_definition_completed | fe05352fe463365132b8f6613d524ae659eef033cfab1c57c99260a77a3a9cc0 | b9c065215cf8875e8e54de9416cac3d500bc97d0e353baa7430a1055af1b6a68 | 21b8b8326fb3c8fc1351550566071bc40c03db05e12d75b4b1274e1e1f107772 | 6c93615dc53ae111bb369c9559adc90c65b27b871469dac4ab99886f82c761b2 | semantic_review_result_v7.json |
| def_1_4 | pass | textbook_definition_completed | 6d0a2047a84de73a9e6540a5e1666ffd6478be7d3a8fc7b0bf1684f7c2c3c244 | 7fadc2e7b5dc47d739fc5e350c6630647b9eb43becac17e071db062065d6e120 | 6adccda1c76ee40b19cb6913e5b08c3a74665d04c4cad8a5f245fd6d0e82187a | 9a4150e92e28cd5b2414344f50acb1a878cbf73e0c5765a608452f0b13fe47c0 | semantic_review_result_v10.json |
| ex_1_2_1 | pass | textbook_source_route_completed | d943da8614dd560035e9bd16ed21f68231815e7cf391832fae3b431a9bf38950 | ce288fa19339ed5fc99cc2392093d2cb330a330f33b20d6eb55d15ce60ec9d3b | fa7710ac90d4151aeb242a800b383651792b4ffc46c0b0ed32d6a4969b2c3b88 | 266be16f9bb0d33572ef476f4d20ee143eaf1c9796688312a3d83bdbf0f2c95e | semantic_review_result_v9.json |
| ex_1_2_2 | pass | textbook_source_route_completed | 7e5412f053fc74a6d4c63ce5fc76f5f7e50cd583b056c22e30db157f68c360cc | e429d4bf4cca8fa3339f50ccbfca9f248d916b6ac6e128d3e91df9385da99d5f | a6023349f693d804775a281985a2b4020a640e0e2dcf26d90d6a1f9f1dedb4d0 | 64e29beca7e28f51feb1735eb57415dbff7cf7dafa1c675f2219350bc3a179f7 | semantic_review_result_v17.json |
| ex_1_2_3 | pass | textbook_source_route_completed | f10ad3a243047bebdc42136335ce7161dfde01f60146e1dbbd2c7ba0cebbe2a1 | 51ca41b43615de7cabeedb8741b590086ff78dbfbb781dfc7ed9581eaff9c082 | 999525213d19aff590ea709430b62834da21134f973d5c437e480db9740e5008 | 727f80949d911722e1b05c97ef443b23498e167129c9198c5b6bdf5a722c9d8b | semantic_review_result_v5.json |
| ex_1_3_1 | pass | textbook_source_route_completed | bce2896ef8aab679365ee1eb28509e59d586ccc0e36061eb1a8b5b74c01f652d | ffcb11e7204c560ea0b9381a5ca82877550258bc7b883f359e49eda7373bc8d1 | 12971b91fda9674d5f6720c52718bdd655274c418bda646d3bf3cae69bbdd605 | 62ff48e85dd239f87a9904ecb0cd2de021ce09d692bf86228ce8cad58df1e8f1 | semantic_review_result_v11.json |
| ex_1_3_2 | pass | textbook_source_route_completed | 67f970b25734251572c5cafbad6240ea84533f4c5fd3fbc497852fbcb2e62915 | 93a3a3577d102e0f584dedfc72fc3bb6d22c67a8535f2c3bf86f61ec5b581f13 | 14158d6f5ab251143a74f79dad83c257141b1ace247f495f0aaaad5f6549fe8f | 770f36692d2e7b237b971906e1786bc4ac526e7cbc2f34e138ce270df022e44f | semantic_review_result_v12.json |
| thm_1_1 | pass | textbook_proof_completed | aa159f6ef278e23b90270deeaff64b2bf0c31b19a068c3da4d29e15ee94ed185 | 94a384975894938e3241b0d02f3590312ef8271d74119c56d27b8140fcdab0a7 | 2008aee1da2eaf5f0bcc31ac690e4fe78d4341cd8fb1e3214bf59dd0b49b42ff | e7e78343dc21ebc87092d123f8029cf62f0dafb4bd3093ea8dd2c376b943d512 | semantic_review_result_v8.json |
| thm_1_2 | pass | textbook_proof_completed | 6ea7b27cf6ac1d6f2b81a54a24b2223fa6d2d41d5b27999249b81595dca3d436 | f0f8914587cb8a424b467c8dda1fd46706f31ee2bcb73588fd79656372c2dc07 | 3bdf03d844f8988c8cd70b8a1befe1b80b48747d7af337695221efd57417e2b1 | f74d90eb0db73c158ff2946c5782cc442f93d31373bb80b8d7fdb089e0803072 | semantic_review_result_v7.json |
| thm_1_3 | pass | source_faithful_proof_completed | 63b583e2e167303a654b58d0f9c79e4184409ec96756959fa76a029729456250 | 0abec285997ed5a3902c040d2ba882c49c8411b7ce2ee82ff2e8c1c47705cfaa | 75b27d24af4fa26b863031188e0b5567f9201a539451e8674417a9c3b4da9358 | 4f19f0581fcf7f2ab7ab3e80c48c9de1734f57b11d9fa32a7024481f750efc2d | semantic_review_result_v10.json |
| thm_1_4 | pass | source_route_proof_completed | 9c0313ac4091c1c817e731117e74aaede51b942bf1ba34da12f038a8fd9c7f38 | a53f1bdd4f292c2adce382e756b8f0f3eac81a41cfa39b829cacdcd1aa570d06 | 8ab87625f587b0987f4da3517ebbf1586eae28334d8f1bd817911bf6af081975 | ad107ca90552faf68041778f923d7414357bbe29df349e70d576320e193d8acb | semantic_review_result_v8.json |
| prob_1_1 | pass | textbook_problem_completed | ceafab900bdf6f34ad97dd6fa451c624bc3562cc127b8a2473e76ff70b9ea0fc | 525dcf9354a44181e67a975e80b1800c0b1f874836d6cdd39ca65566e4eb550d | b24f33290f035b2393da21a04cee7640ea4bb19641f392069971c09b4a9acc61 | 305be74050d39601495ac670c8f1fc5fe759286fa76b366da2be2d61acd4602f | semantic_review_result_v7.json |
| prob_1_2 | pass | textbook_problem_completed | 3dc6e6ecc835863113c765affbdfe5eec3a46cf2515897800fc4e494fefb163e | 38abc6e5972e680d6ef52b044f5cd5804d6277dc45c922d56b9803ae85baaaa0 | cdb7a8f9f7c5836a621b21cc2f00bc329814d64fd417a861b20d0dc036876fe3 | ad760218d343472673dab5f1b673bfe3ebc1a11be3ac2f378c13bcbb346f2fad | semantic_review_result_v13.json |
| prob_1_3 | pass | textbook_problem_completed | 88886f3010b4021f3a0cb1a6ce3c1758c32f6204816aa8d2fc227752af5209bf | aed6736b1c42c96b910dd66a64c22719bafe4e470c7f895278142456d2907584 | d27749e6e6af3d1921fd12adfea4c7ebf05ef1dec74a93dff50be51cc0d0377e | 23ad54dd873acfa3ff11f7257633ab6ae13c80b3a3f421e42797635dac4ee547 | semantic_review_result_v15.json |
| prob_1_4 | pass | textbook_problem_completed | cfa5641582c6daa854f81a13f54bd3ebf714c3cba0693ccf8c543c7d08242f21 | 3b86bbcd9744d06fb65701874b3434d148e02948141f69235259d58d2b8b0409 | f68b0791014fd259d0abd4a45e2a6325f11239484296c6847e7f61fe8c746b7c | 9a2891ee09e73b61afef7e54e48d57e497225151ef72dab12c275a44c3d1c633 | semantic_review_result_v14.json |
| prob_1_5 | pass | textbook_problem_completed | 0164ce7eaf5d1fb227dd4014bc3efad69f7eb3febd52b1f334ae9ad6e8559b19 | ed96a37ba9713ef1c5c8f464a7dd3023b89f25354e6e4c75f6e97221b359fd19 | 555e07b5a258fee530b27a7585506e51c17331891700f3fbcd7e95c1be52b3ea | 02a720c3547012938b11ce808af92dbcafdf450c15c2c863cf8a04ee8d6b81d4 | semantic_review_result_v9.json |
| prob_1_6 | pass | textbook_problem_completed | 1a870b6d3e932354f53412f2627e179fe8db79965105bc68b34919733ec7987c | 57842bad77d9a5faaa78defd2abc082b9d0f69153943e42f6754720c6f6f31bc | 437700a972417ce3323d24e7d1be3ce25e5edeb0933c1315bf582818865e14a1 | f8a17f474c52ea6d9780819c50926e77d640d45b5cfa9fb0fd8e9ab327aae7b2 | semantic_review_result_v12.json |
| prob_1_7 | pass | textbook_problem_completed | f102d30cb3f8d00e6781131ebca431a326b087fce48ede1df387e0aacbc630e2 | 3a55861e79ad7ed27c19fc3dedba03ab399c29fa078459ffa5038283c5051b8e | 9a9562729e3eaef682ce14a5f49c7f4904bd3f3a0fa9fc821ba644ca27c69a88 | c6b7d6f96b180182141b05bb57ee00e133f372a5391d9d7048fda1b825739283 | semantic_review_result_v6.json |
| prob_1_8 | pass | textbook_problem_completed | e9334bd05d186707266c475299c8c9849402d1f7221b7418e940ef877b111057 | aaa37af18df1a91f38ca7c2faa7c4c7db7ec7110b5f4d37f6b2db3fe111743a2 | 1a7671abc4fdd5cf9998c48f9f6d3f3490da249577c323c14b9e42522766c567 | e299c442ceb7c09f45b3552087736f09d60b15d624cef84171e53d6f56c4a36b | semantic_review_result_v13.json |
| prob_1_9 | pass | textbook_problem_completed | 83dca3c189ba0aaee9a44b671877b89d582a757e69905f4b24b5c29d3017af5e | 8738533401ff81ce36f36bf223f9bf05d4f955d7ecda7617bbadb2372d19cd2e | 739d1cc38949f438e71d155dee05926ebd608a55bbae3522c6fb6a2a3ac32af2 | 8a168c4351ac10eac49ae9f4824532f03792f1f17ec40054a65a377e1eb4c4bf | semantic_review_result_v11.json |
| prob_1_10 | pass | source_faithful_proof_completed | ab6458ccae7f5c7003e95c05c4bac93ed1da47d899c088d0efae324f2d06a34a | 6debdcd538fcd2b7eabbab7fb376c8de2b3643ee824d26f2e9493bf4897843dd | 1700cc45b06fe2e13874c8a27dad6feb923e1f7b53939a9fc740f9a3d46e0eec | b0f183b247c3e10da89e5c218a4c7d0f965fadeb180677ecd83856aa2cafe427 | semantic_review_result_v8.json |

## Remaining boundary

The optional whole-line density exhaustion corollary following Definition 1.3 is not claimed. The reviewed Definition 1.3 public contract, whole-line expectation/variance definitions, and Kenneth finite density special case are complete. No exception or blocker remains for the 23 requested tasks.

