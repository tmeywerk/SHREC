(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 2557110876633865 4503599627370496) r3))) (let ((.def_1 (* (- (/ 288296899315423 562949953421312)) r2))) (let ((.def_2 (* (- (/ 1829416842740143 4503599627370496)) r1))) (let ((.def_3 (* (- (/ 5897412606261661 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 3250203578877473 9007199254740992))))) (let ((.def_6 (not b3))) (let ((.def_7 (or .def_6 b1 .def_5))) (let ((.def_8 (* (- (/ 3806777889712683 4503599627370496)) r3))) (let ((.def_9 (* (- (/ 1378349595193191 4503599627370496)) r2))) (let ((.def_10 (* (/ 289068034331581 2251799813685248) r1))) (let ((.def_11 (* (- (/ 1358062579393333 2251799813685248)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 2742328892329733 4503599627370496))))) (let ((.def_14 (not b2))) (let ((.def_15 (not b0))) (let ((.def_16 (or .def_15 .def_14 .def_13))) (let ((.def_17 (* (/ 849892818411181 9007199254740992) r3))) (let ((.def_18 (* (/ 3482063150478179 2251799813685248) r2))) (let ((.def_19 (* (- (/ 2191265690257401 2251799813685248)) r1))) (let ((.def_20 (* (/ 1548367164662481 9007199254740992) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 3880558838159367 4503599627370496)))) (let ((.def_23 (or .def_15 .def_6 .def_22))) (let ((.def_24 (* (/ 945452684620523 9007199254740992) r3))) (let ((.def_25 (* (- (/ 2495296611718003 2251799813685248)) r2))) (let ((.def_26 (* (- (/ 1724196481713957 2251799813685248)) r1))) (let ((.def_27 (* (- (/ 5982798494373773 9007199254740992)) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 8882978954439629 9007199254740992))))) (let ((.def_30 (not b1))) (let ((.def_31 (or .def_14 .def_30 .def_29))) (let ((.def_32 (* (- (/ 860648542650115 2251799813685248)) r3))) (let ((.def_33 (* (- (/ 3779578906209083 9007199254740992)) r2))) (let ((.def_34 (* (- (/ 814466652678907 1125899906842624)) r1))) (let ((.def_35 (* (- (/ 1139076154962619 9007199254740992)) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (- (/ 2778043238773153 4503599627370496))))) (let ((.def_38 (or .def_15 .def_6 .def_37))) (let ((.def_39 (* (/ 754433612511747 4503599627370496) r3))) (let ((.def_40 (* (/ 1249141999974735 2251799813685248) r2))) (let ((.def_41 (* (- (/ 8992651085259473 9007199254740992)) r1))) (let ((.def_42 (* (- (/ 924403696498299 562949953421312)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (- (/ 1976310604625531 4503599627370496))))) (let ((.def_45 (or b1 b2 .def_44))) (let ((.def_46 (* (- (/ 3531123335192071 4503599627370496)) r3))) (let ((.def_47 (* (- (/ 4228922646852305 4503599627370496)) r2))) (let ((.def_48 (* (- (/ 2684110839333481 2251799813685248)) r1))) (let ((.def_49 (* (- (/ 3894362223823883 4503599627370496)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 365887063483211 281474976710656))))) (let ((.def_52 (or .def_15 .def_30 .def_51))) (let ((.def_53 (* (/ 259082305402657 281474976710656) r3))) (let ((.def_54 (* (/ 5669060445153481 9007199254740992) r2))) (let ((.def_55 (* (- (/ 839814683472991 1125899906842624)) r1))) (let ((.def_56 (* (- (/ 5746884470002481 9007199254740992)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 1371197823195227 2251799813685248)))) (let ((.def_59 (or .def_15 b2 .def_58))) (let ((.def_60 (* (/ 8979057998157135 9007199254740992) r3))) (let ((.def_61 (* (/ 2285503283274309 4503599627370496) r2))) (let ((.def_62 (* (- (/ 3589105399590951 4503599627370496)) r1))) (let ((.def_63 (* (/ 3532698950524847 9007199254740992) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 1220459645943499 1125899906842624)))) (let ((.def_66 (or .def_14 b3 .def_65))) (let ((.def_67 (* (- (/ 2657394908039365 2251799813685248)) r3))) (let ((.def_68 (* (/ 1960899999869327 2251799813685248) r2))) (let ((.def_69 (* (/ 1057225580632463 2251799813685248) r1))) (let ((.def_70 (* (- (/ 4788939385853759 9007199254740992)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 1919260068359085 4503599627370496)))) (let ((.def_73 (or .def_15 b1 .def_72))) (let ((.def_74 (* (/ 2857579420826109 4503599627370496) r3))) (let ((.def_75 (* (- (/ 7761355725107667 9007199254740992)) r2))) (let ((.def_76 (* (/ 216332360812889 1125899906842624) r1))) (let ((.def_77 (* (- (/ 87662875717787 35184372088832)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 545439241476201 1125899906842624))))) (let ((.def_80 (or b3 .def_30 .def_79))) (let ((.def_81 (* (- (/ 2698504423002173 9007199254740992)) r3))) (let ((.def_82 (* (- (/ 1170221141437085 2251799813685248)) r2))) (let ((.def_83 (* (/ 3940562637195653 4503599627370496) r1))) (let ((.def_84 (* (/ 1011692848368359 2251799813685248) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 711233588932741 1125899906842624)))) (let ((.def_87 (or b2 b3 .def_86))) (let ((.def_88 (* (/ 2142728791534159 4503599627370496) r3))) (let ((.def_89 (* (- (/ 73970278104287 4503599627370496)) r2))) (let ((.def_90 (* (/ 817566718074913 281474976710656) r1))) (let ((.def_91 (* (/ 3188201050860445 2251799813685248) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (/ 4134177532447489 1125899906842624)))) (let ((.def_94 (or .def_6 b0 .def_93))) (let ((.def_95 (* (- (/ 4113321959849735 4503599627370496)) r3))) (let ((.def_96 (* (/ 3740680097945485 4503599627370496) r2))) (let ((.def_97 (* (/ 3821102275291531 4503599627370496) r1))) (let ((.def_98 (* (- (/ 335450710316049 4503599627370496)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 1048061464318433 1125899906842624)))) (let ((.def_101 (or .def_30 b3 .def_100))) (let ((.def_102 (* (/ 3277563095044287 4503599627370496) r3))) (let ((.def_103 (* (- (/ 3760641612486891 4503599627370496)) r2))) (let ((.def_104 (* (/ 131597660040239 281474976710656) r1))) (let ((.def_105 (* (/ 1907730652297077 4503599627370496) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (/ 3960368976347427 4503599627370496)))) (let ((.def_108 (or b2 .def_15 .def_107))) (let ((.def_109 (* (- (/ 2381562969742545 2251799813685248)) r3))) (let ((.def_110 (* (- (/ 3008979033486547 4503599627370496)) r2))) (let ((.def_111 (* (- (/ 1352057264057031 4503599627370496)) r1))) (let ((.def_112 (* (/ 4110020347744641 9007199254740992) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (- (/ 2806294866858221 9007199254740992))))) (let ((.def_115 (or .def_14 .def_6 .def_114))) (let ((.def_116 (* (/ 3712114151389941 4503599627370496) r3))) (let ((.def_117 (* (- (/ 3150768470775297 4503599627370496)) r2))) (let ((.def_118 (* (- (/ 4145584008587 2199023255552)) r1))) (let ((.def_119 (* (- (/ 843945779891375 9007199254740992)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 715501568343625 4503599627370496))))) (let ((.def_122 (or b0 b2 .def_121))) (let ((.def_123 (* (/ 2398682969323689 2251799813685248) r3))) (let ((.def_124 (* (- (/ 1644751223360065 1125899906842624)) r2))) (let ((.def_125 (* (- (/ 488288371838373 4503599627370496)) r1))) (let ((.def_126 (* (- (/ 2487806226290249 9007199254740992)) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (/ 653245868027601 2251799813685248)))) (let ((.def_129 (or .def_6 .def_14 .def_128))) (let ((.def_130 (and .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_31 .def_23 .def_16 .def_7))) .def_130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
