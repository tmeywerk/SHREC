(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 1360152537181581 2251799813685248)) r3))) (let ((.def_1 (* (- (/ 221031367943745 140737488355328)) r2))) (let ((.def_2 (* (/ 301436726232971 4503599627370496) r1))) (let ((.def_3 (* (- (/ 8730394343653747 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2745729498169857 2251799813685248))))) (let ((.def_6 (* (- (/ 742391068339103 281474976710656)) r3))) (let ((.def_7 (* (- (/ 1371475885095399 2251799813685248)) r2))) (let ((.def_8 (* (/ 4975046737759057 4503599627370496) r1))) (let ((.def_9 (* (/ 101595279938835 1125899906842624) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 8867814670832163 9007199254740992))))) (let ((.def_12 (or b0 .def_11 .def_5))) (let ((.def_13 (* (- (/ 1203128809801203 2251799813685248)) r3))) (let ((.def_14 (* (/ 8210027589901597 9007199254740992) r2))) (let ((.def_15 (* (- (/ 1823008253648739 2251799813685248)) r1))) (let ((.def_16 (* (/ 2216856957371353 4503599627370496) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 110056706522855 281474976710656)))) (let ((.def_19 (* (- (/ 31638292381063 35184372088832)) r3))) (let ((.def_20 (* (- (/ 669272161692697 2251799813685248)) r2))) (let ((.def_21 (* (/ 5772801944936417 9007199254740992) r1))) (let ((.def_22 (* (/ 480282003228503 4503599627370496) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 893419345250039 4503599627370496))))) (let ((.def_25 (not b2))) (let ((.def_26 (or .def_25 .def_24 .def_18))) (let ((.def_27 (* (/ 4688786970474643 9007199254740992) r3))) (let ((.def_28 (* (- (/ 4339807720911381 4503599627370496)) r2))) (let ((.def_29 (* (/ 2150890607425857 4503599627370496) r1))) (let ((.def_30 (* (/ 2032153320476155 9007199254740992) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 1058771418926409 4503599627370496)))) (let ((.def_33 (* (- (/ 3738580829208051 2251799813685248)) r3))) (let ((.def_34 (* (/ 412616496080833 562949953421312) r2))) (let ((.def_35 (* (- (/ 6528525547384983 9007199254740992)) r1))) (let ((.def_36 (* (- (/ 4606834825242415 1125899906842624)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 1787326024150613 562949953421312))))) (let ((.def_39 (or .def_25 .def_38 .def_32))) (let ((.def_40 (* (- (/ 4043459186947505 2251799813685248)) r3))) (let ((.def_41 (* (- (/ 774493715974439 1125899906842624)) r2))) (let ((.def_42 (* (- (/ 243470713668015 562949953421312)) r1))) (let ((.def_43 (* (- (/ 3327241881158043 4503599627370496)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 6921357592039067 4503599627370496))))) (let ((.def_46 (* (/ 7656506402982453 4503599627370496) r3))) (let ((.def_47 (* (/ 3018171035523939 9007199254740992) r2))) (let ((.def_48 (* (- (/ 2018538534853771 2251799813685248)) r1))) (let ((.def_49 (* (- (/ 8858766500556777 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 1683952302812149 9007199254740992))))) (let ((.def_52 (or .def_25 .def_51 .def_45))) (let ((.def_53 (* (/ 2777304219540495 2251799813685248) r3))) (let ((.def_54 (* (- (/ 599334428935389 562949953421312)) r2))) (let ((.def_55 (* (- (/ 799743219090393 562949953421312)) r1))) (let ((.def_56 (* (/ 4036181015728839 9007199254740992) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 20040089564519 9007199254740992)))) (let ((.def_59 (* (/ 7169860054606835 9007199254740992) r3))) (let ((.def_60 (* (/ 7662391495601545 9007199254740992) r2))) (let ((.def_61 (* (- (/ 2016087391409359 9007199254740992)) r1))) (let ((.def_62 (* (/ 433766541982355 562949953421312) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 4671360621960279 4503599627370496)))) (let ((.def_65 (or b3 .def_64 .def_58))) (let ((.def_66 (* (- (/ 64979793451619 562949953421312)) r3))) (let ((.def_67 (* (/ 2260390415497273 9007199254740992) r2))) (let ((.def_68 (* (- (/ 3563676644810881 4503599627370496)) r1))) (let ((.def_69 (* (/ 7121766920386163 9007199254740992) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 2556683060258817 9007199254740992)))) (let ((.def_72 (* (/ 449830057374353 281474976710656) r3))) (let ((.def_73 (* (/ 3293595151195965 4503599627370496) r2))) (let ((.def_74 (* (- (/ 1519121751721929 1125899906842624)) r1))) (let ((.def_75 (* (- (/ 4464206370565103 2251799813685248)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (- (/ 5806261486878243 9007199254740992))))) (let ((.def_78 (not b3))) (let ((.def_79 (or .def_78 .def_77 .def_71))) (let ((.def_80 (* (/ 47744678708173 35184372088832) r3))) (let ((.def_81 (* (- (/ 49535035560875 281474976710656)) r2))) (let ((.def_82 (* (- (/ 8399831584417319 9007199254740992)) r1))) (let ((.def_83 (* (/ 7421731351385479 9007199254740992) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 1563774934735675 2251799813685248)))) (let ((.def_86 (* (- (/ 4074975934154461 2251799813685248)) r3))) (let ((.def_87 (* (- (/ 1520268539277603 2251799813685248)) r2))) (let ((.def_88 (* (/ 1155758410793447 4503599627370496) r1))) (let ((.def_89 (* (/ 2909924498096957 4503599627370496) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (- (/ 7307543374704287 9007199254740992))))) (let ((.def_92 (or .def_25 .def_91 .def_85))) (let ((.def_93 (* (/ 4919101679001945 9007199254740992) r3))) (let ((.def_94 (* (- (/ 1240279966279907 1125899906842624)) r2))) (let ((.def_95 (* (- (/ 7177700231394991 9007199254740992)) r1))) (let ((.def_96 (* (/ 374352078642565 2251799813685248) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 674505098653337 9007199254740992))))) (let ((.def_99 (* (- (/ 895054356819359 562949953421312)) r3))) (let ((.def_100 (* (- (/ 3458349063446815 9007199254740992)) r2))) (let ((.def_101 (* (- (/ 301983525156989 140737488355328)) r1))) (let ((.def_102 (* (/ 3881261653782265 4503599627370496) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (- (/ 3855710962787677 2251799813685248))))) (let ((.def_105 (or b2 .def_104 .def_98))) (let ((.def_106 (* (/ 242821709069919 4503599627370496) r3))) (let ((.def_107 (* (/ 7760102676224505 9007199254740992) r2))) (let ((.def_108 (* (/ 1631107054450561 2251799813685248) r1))) (let ((.def_109 (* (- (/ 527878010184673 1125899906842624)) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 6030031904063981 9007199254740992)))) (let ((.def_112 (* (- (/ 3395073584923695 9007199254740992)) r3))) (let ((.def_113 (* (- (/ 2881920287063115 4503599627370496)) r2))) (let ((.def_114 (* (- (/ 3389028312202525 2251799813685248)) r1))) (let ((.def_115 (* (- (/ 2070720531202989 9007199254740992)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 3262539765015005 2251799813685248))))) (let ((.def_118 (not b1))) (let ((.def_119 (or .def_118 .def_117 .def_111))) (let ((.def_120 (* (/ 891317934898439 4503599627370496) r3))) (let ((.def_121 (* (- (/ 4467172268140577 4503599627370496)) r2))) (let ((.def_122 (* (/ 143370677577619 4503599627370496) r1))) (let ((.def_123 (* (- (/ 4707210502037381 2251799813685248)) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (- (/ 5926304165664087 9007199254740992))))) (let ((.def_126 (* (/ 4165988508679357 2251799813685248) r3))) (let ((.def_127 (* (- (/ 84175202401359 281474976710656)) r2))) (let ((.def_128 (* (- (/ 4239401136362569 4503599627370496)) r1))) (let ((.def_129 (* (- (/ 105587972986639 281474976710656)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 728807351982589 9007199254740992)))) (let ((.def_132 (not b0))) (let ((.def_133 (or .def_132 .def_131 .def_125))) (let ((.def_134 (and .def_133 .def_119 .def_105 .def_92 .def_79 .def_65 .def_52 .def_39 .def_26 .def_12))) .def_134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
