(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 2697860780818009 1125899906842624)) r3))) (let ((.def_1 (* (- (/ 1794965313284845 2251799813685248)) r2))) (let ((.def_2 (* (/ 3846239846697789 9007199254740992) r1))) (let ((.def_3 (* (/ 7805230232142859 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 299560148309481 281474976710656))))) (let ((.def_6 (* (/ 3133229282130069 4503599627370496) r3))) (let ((.def_7 (* (/ 1941241178987607 2251799813685248) r2))) (let ((.def_8 (* (- (/ 160250276512553 1125899906842624)) r1))) (let ((.def_9 (* (- (/ 1386687898433597 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 1033452875798733 2251799813685248)))) (let ((.def_12 (or b3 .def_11 .def_5))) (let ((.def_13 (* (/ 617077590111445 9007199254740992) r3))) (let ((.def_14 (* (/ 2655528304731643 2251799813685248) r2))) (let ((.def_15 (* (- (/ 4079790132970131 9007199254740992)) r1))) (let ((.def_16 (* (- (/ 4070724837541323 9007199254740992)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 2012552067442387 9007199254740992)))) (let ((.def_19 (* (/ 1653713067504587 4503599627370496) r3))) (let ((.def_20 (* (- (/ 6462094803304187 9007199254740992)) r2))) (let ((.def_21 (* (/ 1404246143694791 1125899906842624) r1))) (let ((.def_22 (* (- (/ 3781193203370261 4503599627370496)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 217649609663981 4503599627370496))))) (let ((.def_25 (or b0 .def_24 .def_18))) (let ((.def_26 (* (- (/ 1417438962811937 4503599627370496)) r3))) (let ((.def_27 (* (/ 665409932272935 562949953421312) r2))) (let ((.def_28 (* (/ 1565006320363889 2251799813685248) r1))) (let ((.def_29 (* (- (/ 2555439323589577 4503599627370496)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (/ 101685785669691 281474976710656)))) (let ((.def_32 (* (- (/ 220366322710969 4503599627370496)) r3))) (let ((.def_33 (* (- (/ 2670884353425819 2251799813685248)) r2))) (let ((.def_34 (* (- (/ 5973769009217329 9007199254740992)) r1))) (let ((.def_35 (* (/ 2256651247599711 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (- (/ 1251668857028495 2251799813685248))))) (let ((.def_38 (not b1))) (let ((.def_39 (or .def_38 .def_37 .def_31))) (let ((.def_40 (* (- (/ 5881752353716319 4503599627370496)) r3))) (let ((.def_41 (* (/ 6890617917101943 9007199254740992) r2))) (let ((.def_42 (* (- (/ 27069497847283 17592186044416)) r1))) (let ((.def_43 (* (- (/ 3457115815734141 2251799813685248)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 998182358821117 562949953421312))))) (let ((.def_46 (* (- (/ 136723474858503 562949953421312)) r3))) (let ((.def_47 (* (- (/ 1780038059722891 4503599627370496)) r2))) (let ((.def_48 (* (/ 1297263351827161 4503599627370496) r1))) (let ((.def_49 (* (/ 1845239321590877 1125899906842624) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 1353019453594957 2251799813685248)))) (let ((.def_52 (not b2))) (let ((.def_53 (or .def_52 .def_51 .def_45))) (let ((.def_54 (* (/ 2815636418454089 2251799813685248) r3))) (let ((.def_55 (* (- (/ 2542466128119305 4503599627370496)) r2))) (let ((.def_56 (* (/ 2370727883311265 2251799813685248) r1))) (let ((.def_57 (* (- (/ 4824430514143049 9007199254740992)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 2986279752275919 4503599627370496)))) (let ((.def_60 (* (- (/ 62810917844617 4503599627370496)) r3))) (let ((.def_61 (* (/ 8181261992427205 9007199254740992) r2))) (let ((.def_62 (* (- (/ 3895599388287283 2251799813685248)) r1))) (let ((.def_63 (* (/ 3261536120406417 9007199254740992) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 2872797030802909 9007199254740992))))) (let ((.def_66 (or b3 .def_65 .def_59))) (let ((.def_67 (* (- (/ 362303627859831 2251799813685248)) r3))) (let ((.def_68 (* (- (/ 2100413432667197 9007199254740992)) r2))) (let ((.def_69 (* (/ 3776200688826949 4503599627370496) r1))) (let ((.def_70 (* (- (/ 3934711032324331 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 2009041343665063 9007199254740992))))) (let ((.def_73 (* (- (/ 1067298449033289 1125899906842624)) r3))) (let ((.def_74 (* (- (/ 2622042492702725 1125899906842624)) r2))) (let ((.def_75 (* (/ 1047512399991725 4503599627370496) r1))) (let ((.def_76 (* (/ 2502494322879445 2251799813685248) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 169324458082407 140737488355328))))) (let ((.def_79 (not b0))) (let ((.def_80 (or .def_79 .def_78 .def_72))) (let ((.def_81 (* (- (/ 2973642211519795 2251799813685248)) r3))) (let ((.def_82 (* (- (/ 1498820600058067 4503599627370496)) r2))) (let ((.def_83 (* (/ 449669241510685 1125899906842624) r1))) (let ((.def_84 (* (/ 2792615825300727 4503599627370496) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 140371984484399 2251799813685248)))) (let ((.def_87 (* (- (/ 2234643801975889 2251799813685248)) r3))) (let ((.def_88 (* (- (/ 8456476844674919 9007199254740992)) r2))) (let ((.def_89 (* (/ 5954088992360749 4503599627370496) r1))) (let ((.def_90 (* (- (/ 4161561776476443 2251799813685248)) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (- (/ 1657692068642657 1125899906842624))))) (let ((.def_93 (or .def_38 .def_92 .def_86))) (let ((.def_94 (* (/ 2551082604652225 9007199254740992) r3))) (let ((.def_95 (* (- (/ 716689063499671 4503599627370496)) r2))) (let ((.def_96 (* (- (/ 1536512225427707 1125899906842624)) r1))) (let ((.def_97 (* (- (/ 5559652965462225 4503599627370496)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 3212387311091783 4503599627370496))))) (let ((.def_100 (* (- (/ 2421944981076971 4503599627370496)) r3))) (let ((.def_101 (* (/ 3098271563847441 4503599627370496) r2))) (let ((.def_102 (* (/ 1199167523012037 4503599627370496) r1))) (let ((.def_103 (* (- (/ 6708746891260865 9007199254740992)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 236286749851025 1125899906842624))))) (let ((.def_106 (or .def_38 .def_105 .def_99))) (let ((.def_107 (and .def_106 .def_93 .def_80 .def_66 .def_53 .def_39 .def_25 .def_12))) .def_107)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
