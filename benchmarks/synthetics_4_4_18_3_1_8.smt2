(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (- (/ 7150985899051361 9007199254740992)) r3))) (let ((.def_1 (* (/ 5589260410193179 4503599627370496) r2))) (let ((.def_2 (* (- (/ 3828479840785217 2251799813685248)) r1))) (let ((.def_3 (* (- (/ 465174898073517 1125899906842624)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2485925706240653 9007199254740992))))) (let ((.def_6 (not b1))) (let ((.def_7 (or b3 .def_6 .def_5))) (let ((.def_8 (* (/ 712579858114785 1125899906842624) r3))) (let ((.def_9 (* (/ 895020434807779 4503599627370496) r2))) (let ((.def_10 (* (/ 1828967078237999 2251799813685248) r1))) (let ((.def_11 (* (- (/ 7281454616149319 4503599627370496)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 2046017249946353 4503599627370496)))) (let ((.def_14 (not b2))) (let ((.def_15 (or .def_14 b1 .def_13))) (let ((.def_16 (* (- (/ 1983082402090225 4503599627370496)) r3))) (let ((.def_17 (* (- (/ 534924910672403 1125899906842624)) r2))) (let ((.def_18 (* (/ 602008905206997 4503599627370496) r1))) (let ((.def_19 (* (- (/ 1131316297635835 1125899906842624)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 3402144547403909 4503599627370496))))) (let ((.def_22 (or b3 b2 .def_21))) (let ((.def_23 (* (- (/ 33170895759343 35184372088832)) r3))) (let ((.def_24 (* (- (/ 141342491263113 562949953421312)) r2))) (let ((.def_25 (* (/ 2565374823084501 4503599627370496) r1))) (let ((.def_26 (* (- (/ 335825086465315 562949953421312)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 1744993405509475 4503599627370496))))) (let ((.def_29 (not b0))) (let ((.def_30 (or .def_29 b3 .def_28))) (let ((.def_31 (* (- (/ 24929414429217 562949953421312)) r3))) (let ((.def_32 (* (- (/ 763035965920907 2251799813685248)) r2))) (let ((.def_33 (* (/ 3046928834285841 4503599627370496) r1))) (let ((.def_34 (* (- (/ 1103752768433777 2251799813685248)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 1776631994237 8796093022208)))) (let ((.def_37 (or .def_29 .def_14 .def_36))) (let ((.def_38 (* (- (/ 1463223832229141 4503599627370496)) r3))) (let ((.def_39 (* (/ 1102909644073831 4503599627370496) r2))) (let ((.def_40 (* (- (/ 140359591333805 4503599627370496)) r1))) (let ((.def_41 (* (/ 1785015413105115 4503599627370496) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 3116391143020001 9007199254740992)))) (let ((.def_44 (or b1 .def_29 .def_43))) (let ((.def_45 (* (- (/ 6573674245635931 9007199254740992)) r3))) (let ((.def_46 (* (- (/ 8857692971881885 9007199254740992)) r2))) (let ((.def_47 (* (/ 1755049236294581 2251799813685248) r1))) (let ((.def_48 (* (- (/ 2379859819763969 1125899906842624)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 6873189492873893 9007199254740992))))) (let ((.def_51 (or b2 b0 .def_50))) (let ((.def_52 (* (- (/ 6520114345108617 9007199254740992)) r3))) (let ((.def_53 (* (- (/ 2632013117839599 2251799813685248)) r2))) (let ((.def_54 (* (- (/ 4416135007347871 4503599627370496)) r1))) (let ((.def_55 (* (- (/ 1575520641822647 4503599627370496)) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (- (/ 1219945810933891 1125899906842624))))) (let ((.def_58 (or b3 .def_6 .def_57))) (let ((.def_59 (* (/ 4481261631635563 4503599627370496) r3))) (let ((.def_60 (* (/ 6519582972433881 9007199254740992) r2))) (let ((.def_61 (* (- (/ 1817988712917443 1125899906842624)) r1))) (let ((.def_62 (* (- (/ 3006306479059325 2251799813685248)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 790013115028403 2251799813685248)))) (let ((.def_65 (or .def_6 b2 .def_64))) (let ((.def_66 (* (/ 3060187412028819 4503599627370496) r3))) (let ((.def_67 (* (- (/ 182908563639297 2251799813685248)) r2))) (let ((.def_68 (* (- (/ 516048076112371 2251799813685248)) r1))) (let ((.def_69 (* (- (/ 723894556444893 4503599627370496)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 1653731862769705 4503599627370496)))) (let ((.def_72 (or .def_14 b1 .def_71))) (let ((.def_73 (* (- (/ 2242489787365819 2251799813685248)) r3))) (let ((.def_74 (* (- (/ 2066382097055675 2251799813685248)) r2))) (let ((.def_75 (* (/ 1977292114961085 1125899906842624) r1))) (let ((.def_76 (* (/ 2974197433023981 4503599627370496) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (/ 1948574265404661 2251799813685248)))) (let ((.def_79 (or .def_29 .def_6 .def_78))) (let ((.def_80 (* (/ 39434910815507 1125899906842624) r3))) (let ((.def_81 (* (- (/ 1459902859492181 2251799813685248)) r2))) (let ((.def_82 (* (- (/ 1844027708654901 9007199254740992)) r1))) (let ((.def_83 (* (/ 3098654215022991 4503599627370496) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 157774450902605 562949953421312)))) (let ((.def_86 (or .def_6 b2 .def_85))) (let ((.def_87 (* (/ 215836589701271 2251799813685248) r3))) (let ((.def_88 (* (- (/ 536365883691867 2251799813685248)) r2))) (let ((.def_89 (* (- (/ 872327238977943 2251799813685248)) r1))) (let ((.def_90 (* (- (/ 679976841206271 1125899906842624)) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (- (/ 1355316918603769 4503599627370496))))) (let ((.def_93 (or b1 b2 .def_92))) (let ((.def_94 (* (- (/ 2706237746433705 4503599627370496)) r3))) (let ((.def_95 (* (- (/ 4244965475588039 4503599627370496)) r2))) (let ((.def_96 (* (- (/ 4349776249286043 4503599627370496)) r1))) (let ((.def_97 (* (/ 3168206496680193 4503599627370496) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 1408915234328533 4503599627370496))))) (let ((.def_100 (or .def_14 b3 .def_99))) (let ((.def_101 (* (- (/ 5567958728872197 2251799813685248)) r3))) (let ((.def_102 (* (- (/ 2388518415284595 4503599627370496)) r2))) (let ((.def_103 (* (- (/ 4250663917452495 9007199254740992)) r1))) (let ((.def_104 (* (/ 357638343882495 9007199254740992) r0))) (let ((.def_105 (+ .def_104 .def_103 .def_102 .def_101))) (let ((.def_106 (<= .def_105 (- (/ 3947570929923457 4503599627370496))))) (let ((.def_107 (not b3))) (let ((.def_108 (or .def_107 b2 .def_106))) (let ((.def_109 (* (- (/ 3830614954308269 4503599627370496)) r3))) (let ((.def_110 (* (- (/ 1188385320329199 9007199254740992)) r2))) (let ((.def_111 (* (/ 3729474080420209 4503599627370496) r1))) (let ((.def_112 (* (/ 2304189233525243 4503599627370496) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 2659342776006649 4503599627370496)))) (let ((.def_115 (or b2 .def_107 .def_114))) (let ((.def_116 (* (- (/ 621215130222025 1125899906842624)) r3))) (let ((.def_117 (* (/ 1177520044969755 1125899906842624) r2))) (let ((.def_118 (* (- (/ 125256949907493 140737488355328)) r1))) (let ((.def_119 (* (/ 1195803855259039 2251799813685248) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (/ 5824118389003463 9007199254740992)))) (let ((.def_122 (or .def_6 .def_107 .def_121))) (let ((.def_123 (* (- (/ 979031555633285 4503599627370496)) r3))) (let ((.def_124 (* (/ 1479555681553819 2251799813685248) r2))) (let ((.def_125 (* (/ 1697347934452075 9007199254740992) r1))) (let ((.def_126 (* (- (/ 472353619658251 1125899906842624)) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (/ 61617811984473 140737488355328)))) (let ((.def_129 (or b3 .def_14 .def_128))) (let ((.def_130 (and .def_129 .def_122 .def_115 .def_108 .def_100 .def_93 .def_86 .def_79 .def_72 .def_65 .def_58 .def_51 .def_44 .def_37 .def_30 .def_22 .def_15 .def_7))) .def_130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)