(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (/ 799153150016661 4503599627370496) r3))) (let ((.def_1 (* (- (/ 572002676165753 562949953421312)) r2))) (let ((.def_2 (* (- (/ 1016961130636129 9007199254740992)) r1))) (let ((.def_3 (* (/ 288124101717091 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 432414313892419 2251799813685248))))) (let ((.def_6 (not b3))) (let ((.def_7 (or b2 .def_6 .def_5))) (let ((.def_8 (* (/ 549611010496491 2251799813685248) r3))) (let ((.def_9 (* (/ 1559311717041561 1125899906842624) r2))) (let ((.def_10 (* (/ 3574942748773477 2251799813685248) r1))) (let ((.def_11 (* (- (/ 3676832309619045 4503599627370496)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 4131253657028849 2251799813685248)))) (let ((.def_14 (not b2))) (let ((.def_15 (not b0))) (let ((.def_16 (or .def_15 .def_14 .def_13))) (let ((.def_17 (* (- (/ 2934224987996733 4503599627370496)) r3))) (let ((.def_18 (* (- (/ 128822548820413 4503599627370496)) r2))) (let ((.def_19 (* (- (/ 404664124763741 1125899906842624)) r1))) (let ((.def_20 (* (- (/ 5310208895038003 9007199254740992)) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (- (/ 2639839907304697 4503599627370496))))) (let ((.def_23 (or b2 b1 .def_22))) (let ((.def_24 (* (/ 451929500994531 4503599627370496) r3))) (let ((.def_25 (* (/ 1717509307426033 4503599627370496) r2))) (let ((.def_26 (* (/ 5842392938305487 9007199254740992) r1))) (let ((.def_27 (* (/ 3861644567638623 4503599627370496) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (/ 6456389494718181 4503599627370496)))) (let ((.def_30 (or .def_15 .def_14 .def_29))) (let ((.def_31 (* (- (/ 66705551823737 35184372088832)) r3))) (let ((.def_32 (* (- (/ 8472335157410425 9007199254740992)) r2))) (let ((.def_33 (* (/ 403314757448911 4503599627370496) r1))) (let ((.def_34 (* (- (/ 1487932058761581 9007199254740992)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 4447272671055915 4503599627370496))))) (let ((.def_37 (or b1 b0 .def_36))) (let ((.def_38 (* (/ 2588631253845229 4503599627370496) r3))) (let ((.def_39 (* (- (/ 8674302111662823 9007199254740992)) r2))) (let ((.def_40 (* (- (/ 4913472730081725 2251799813685248)) r1))) (let ((.def_41 (* (/ 38844521970139 562949953421312) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 1480625405976319 2251799813685248))))) (let ((.def_44 (or b0 b1 .def_43))) (let ((.def_45 (* (- (/ 364448985574241 1125899906842624)) r3))) (let ((.def_46 (* (- (/ 2733578788374151 2251799813685248)) r2))) (let ((.def_47 (* (- (/ 1087956807961397 2251799813685248)) r1))) (let ((.def_48 (* (- (/ 4451466067226437 9007199254740992)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 2018546677504449 2251799813685248))))) (let ((.def_51 (not b1))) (let ((.def_52 (or .def_51 .def_15 .def_50))) (let ((.def_53 (* (- (/ 890012035947417 1125899906842624)) r3))) (let ((.def_54 (* (- (/ 945878728563199 2251799813685248)) r2))) (let ((.def_55 (* (/ 4404757395316091 4503599627370496) r1))) (let ((.def_56 (* (- (/ 1484138491413153 1125899906842624)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 3173794486138951 9007199254740992))))) (let ((.def_59 (or b2 b0 .def_58))) (let ((.def_60 (* (/ 2817955320288875 1125899906842624) r3))) (let ((.def_61 (* (- (/ 979450973970317 562949953421312)) r2))) (let ((.def_62 (* (- (/ 1302742783535821 2251799813685248)) r1))) (let ((.def_63 (* (- (/ 3342990524240355 4503599627370496)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 2288364264778403 4503599627370496)))) (let ((.def_66 (or .def_14 .def_6 .def_65))) (let ((.def_67 (* (/ 480637693468547 1125899906842624) r3))) (let ((.def_68 (* (/ 37128484229105 70368744177664) r2))) (let ((.def_69 (* (- (/ 2396577250376201 2251799813685248)) r1))) (let ((.def_70 (* (- (/ 1769669147003345 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 550230359964465 9007199254740992))))) (let ((.def_73 (or .def_15 .def_14 .def_72))) (let ((.def_74 (* (/ 3821227905105071 4503599627370496) r3))) (let ((.def_75 (* (- (/ 949234156559731 562949953421312)) r2))) (let ((.def_76 (* (- (/ 592938167616249 9007199254740992)) r1))) (let ((.def_77 (* (- (/ 1912692394388683 4503599627370496)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 316409949256827 9007199254740992)))) (let ((.def_80 (or b2 b1 .def_79))) (let ((.def_81 (* (/ 155846969499963 281474976710656) r3))) (let ((.def_82 (* (- (/ 3281584155932009 2251799813685248)) r2))) (let ((.def_83 (* (- (/ 709309872886067 4503599627370496)) r1))) (let ((.def_84 (* (- (/ 1451659612380421 9007199254740992)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 797217978274507 2251799813685248))))) (let ((.def_87 (or .def_51 b3 .def_86))) (let ((.def_88 (* (- (/ 2331919829750901 2251799813685248)) r3))) (let ((.def_89 (* (- (/ 2633646106822891 1125899906842624)) r2))) (let ((.def_90 (* (- (/ 8116759790362813 9007199254740992)) r1))) (let ((.def_91 (* (- (/ 1993614250677233 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 5787259216903367 4503599627370496))))) (let ((.def_94 (or .def_6 b0 .def_93))) (let ((.def_95 (* (/ 4140030235490959 4503599627370496) r3))) (let ((.def_96 (* (- (/ 39917654250891 140737488355328)) r2))) (let ((.def_97 (* (/ 416440575151153 4503599627370496) r1))) (let ((.def_98 (* (- (/ 2826879117049455 4503599627370496)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 4270907394853665 9007199254740992)))) (let ((.def_101 (or b1 b3 .def_100))) (let ((.def_102 (* (- (/ 2376833613788567 4503599627370496)) r3))) (let ((.def_103 (* (- (/ 4618063571728025 2251799813685248)) r2))) (let ((.def_104 (* (/ 688961399441865 4503599627370496) r1))) (let ((.def_105 (* (/ 2227953166297393 4503599627370496) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 822197200822775 4503599627370496))))) (let ((.def_108 (or b2 b3 .def_107))) (let ((.def_109 (* (/ 4081060915760555 2251799813685248) r3))) (let ((.def_110 (* (- (/ 707421704586971 562949953421312)) r2))) (let ((.def_111 (* (- (/ 173131802921763 1125899906842624)) r1))) (let ((.def_112 (* (- (/ 549151131372729 2251799813685248)) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 3864492540853765 4503599627370496)))) (let ((.def_115 (or .def_51 b3 .def_114))) (let ((.def_116 (* (- (/ 8039587367531131 9007199254740992)) r3))) (let ((.def_117 (* (- (/ 333909144345739 4503599627370496)) r2))) (let ((.def_118 (* (- (/ 1843108754585251 1125899906842624)) r1))) (let ((.def_119 (* (- (/ 1291392303171263 562949953421312)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 3817340814655207 2251799813685248))))) (let ((.def_122 (or b0 .def_51 .def_121))) (let ((.def_123 (and .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_37 .def_30 .def_23 .def_16 .def_7))) .def_123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)