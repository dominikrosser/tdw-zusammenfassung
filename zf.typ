#import "@preview/physica:0.7.5": *
#import "@preview/colorful-boxes:1.0.0": colorbox
#import "@preview/tablex:0.0.5": tablex, colspanx, rowspanx, cellx

#set page(
    "a4",
    flipped: true,
    margin: (x: 0.25cm, y: 0.25cm))
#let tablex = tablex.with(spacing: 0em)

#set text(size: 11pt)
#let defbox = colorbox.with(color: "blue")
#let thmbox = colorbox.with(color: "green")
#let modellbox = colorbox.with(color: "yellow")
#let eqbox = box.with(stroke: gray.lighten(30%), inset: 3pt)
#let eqnametext = text.with(fill: gray.lighten(30%), size: 6pt)
#let padeqbox = box.with(stroke: gray.lighten(35%), inset: 5pt)
#let condbox = box.with(stroke: orange.lighten(70%), inset: 3pt) // For conditional statements that are not always true
#let padcondbox = condbox.with(inset: 6pt)
#let condtext = text.with(fill: orange.lighten(70%), size: 6pt) // For conditional statements that are not always true, text thas says when true
#let subbox = box.with(stroke: black.lighten(50%), inset: 5pt)

//#box(width: 100%, height: auto)[
#columns(3, gutter: 0.25cm)[

#tablex(
    columns: 2,
    [$p$ #underline("wirkt") auf $S$], [$exists A in "Atom"(S): floor(p)_A "def."$],
    [$p$ #underline("arbeitsprozess") auf $S$], [$floor(p)_(S')$ def gdw. $S' in "Sub"(S)$],
    [$p$ #underline("zyklisch") auf $S$], [$floor(p)_S = ceil(p)_S$],
    [$p$ #underline("identitäts-proz.") auf $S$], [$p in cal(P)_S$ und $floor(p)_S = ceil(p)_S$],
    [$p in cal(P)_S$ #underline("reversibel")], [$exists p^"rev" in cal(P)_S: p^"rev" compose p eq.triple "id"_S$ $arrow.double W_(S)(p^"rev") = - W_(S)(p)$],
    [#underline("Arbeit") $W_S$], [$W_A: cal(P) arrow RR$, $W_(A)(p' compose p) = W_(A)(p) + W_(A)(p')$],
    [#underline("Zustandsgrösse") $Z$\ von $S$], [$Z: Sigma_S arrow RR^n$, $Delta Z(p) := Z(sigma) - Z(sigma_0)$\ $delta E = dd(E) = pdv(E,x)dd(x) + pdv(E,y)dd(y)$],
    [#underline("innere Energie") $U_S$], [$U_S: Sigma_S arrow RR text("ist Zustandsgr.")$, $Delta U_(S)(p' compose p) = Delta U(p) + Delta U(p')$, $Delta U_(A or B) = Delta U_A + Delta U_B$, $p in cal(P)_S arrow.double W_S = Delta U_S$],
    [#underline("Wärme") $Q_S$ (hin zu)], [$Q_(S)(p) := Delta U_(S)(p) - W_(S)(p)$, $Q_(S)(p' compose p) = Q_(S)(p) + Q_(S)(p')$, $Q_(A or B)(p) = Q_(A)(p) + Q_(B)(p)$, $p in cal(P)_S arrow.double Q_(S)(p) = 0$, $p text("zykl.") arrow.double Q_(S)(p) = -W_(S)(p)$, und $integral.cont delta Q_A = - integral.cont delta W_A$],
    [$p in cal(P)_S$ #underline("quasistatisch")], [$floor(p(lambda, lambda')), ceil(p(lambda, lambda')) = sigma_lambda, sigma_(lambda')$],
    [differenzielle Grössen], [$Delta U_A = integral_(sigma_lambda)^(sigma_(lambda')) dd(U)_A$, $W_A = integral_(sigma_lambda)^(sigma_(lambda')) delta W_A$, $delta Q_A = dd(U)_A - delta W_A$],
    [$p$ #underline("adiabatisch") auf $S$], [$p$ quasistatisch und $delta Q_S = 0$],
    [$R$ #underline("Reservoir")], [$U_R: Sigma_R arrow RR text("injektiv")$, $forall p: W_(R)(p) >= 0$, $forall p_"wirkend(S)", forall Delta U exists \"T_(Delta U)(p)\"$, $arrow.double forall U_(R)(sigma_2) >= U_(R)(sigma_1):$ $exists p in cal(P)_R [sigma_1 arrow sigma_2]$],
    [#underline("Absolute Temperatur") $T$], [$T := tau(R, R_"ref")T_"ref"$, wobei\ $tau(R_1, R_2) := -(Q_(R_1)(p))/(Q_(R_2)(p))$],
)
$cal(A)$, $cal(S)$, $cal(P)$, $"Sub"(S)$, $"Atom"(S)$, $Sigma_A$, $Sigma_S$, $cal(R)$, $cal(P)_S$, $floor(p)_S, ceil(p)_S$
/////////////////
#tablex(
    columns: (42%, 58%),
    [Interne Energie], [$U(S, V, N) = integral dd(U)$\ $dd(U) = T dd(S) - p dd(V) + mu dd(N)$],
    [Entropie], [$S(U, V, N) = 1/T (U + p V - mu N)$\ $dd(S) = 1/T (dd(U) + p dd(V) - mu dd(N))$],
    [Helmholz Free Energy\ ($-U^(*(S arrow T))$)], [$F(T, V, N) = U - T S$\ $dd(F) = -S dd(T) - p dd(V) + mu dd(N)$],
    [Enthalpie\ ($-U^(*(V arrow -p))$)], [$H(S, p, N) = U + p V$\ $dd(H) = T dd(S) + V dd(p) + mu dd(N)$],
    [Gibbs Free Energy\ ($-U^(*((V,S) arrow (-p,Τ)))$)], [$G(T,p,N) = U + p V - T S$\ $dd(G) = -S dd(T) + V dd(p) + mu dd(N)$],
    [Grand Potential\ ($-U^(*((S,N) arrow (T, mu)))$)], [$Omega(T,V,mu) = U - T S - mu N$\ $dd(Omega) = -S dd(T) - p dd(V) - N dd(mu)$],
//)
//#tablex(
//    columns: 2,
    [*Maxwell's Relations*\ $eval(pdv(T,V))_S = -eval(pdv(P,S))_V$, $eval(pdv(T,P))_S = eval(pdv(V,S))_P$, $eval(pdv(S,V))_T = eval(pdv(P,T))_V$, $eval(pdv(S,P))_T = -eval(pdv(T,V))_P$], [*Other relations*\ $eval(pdv(S,U))_(V,N) = 1/T$, $eval(pdv(S,V))_(N,U) = p/T$, $eval(pdv(S,N))_(V,U) = -mu/T$\ $eval(pdv(T,S))_V = T/C_V$, $eval(pdv(T,S))_P = T/C_P$, $eval(pdv(p,V))_T = (-1)/(V K_T)$],
    colspanx(2)[*Gibbs-Helmholtz Equations*\ $H = -T^2 eval(pdv((G/T),T))_p$, $eval(pdv(H,p))_T = V - T eval(pdv(V,T))_P$, $U = -T^2 eval(pdv((F/T),T))_V$, $eval(pdv(U,V))_T = T eval(pdv(P,T))_V - P$, $G = -V^2 eval(pdv((F/V),V))_T$],
    [*Gibbs-Duhem Eq.*],[$S dd(T) - V dd(p) + N dd(mu) = 0$],
    [*Euler-Gleichung*], [$U = T S - p V + mu N$],
    colspanx(2)[#underline("Carnot-Maschine"): $(S, R_1, R_2, p in cal(P)_(S or R_1 or R_2) "zykl"(S))$\ $forall i: W_(R_i)(p) = 0$, und $exists i: Q_(R_i)(p) eq.not 0$. $"rev" arrow.l.r p "rev"$.],
    cellx(colspan: 2, fill: gray.lighten(60%))[$(S, R_1, R_2, p)$ eine Carnot-Maschine. OBDA $Q_(R_2) > 0$.],
    cellx(fill: gray.lighten(60%))[#underline("Wärmekraftmaschine") $W_(S) < 0 arrow.double Q_(R_1) < 0$\ Effizienz: ($T_2 < T_1$)\ $eta = abs(W_(S)(p))/abs(Q_(R_1)(p)) <= 1 - T_2/T_1$\ $eta_"rev" = eta_C := 1 - T_2/T_1$],
    cellx(fill: gray.lighten(60%))[#underline("Wärmepumpe")\ $T_2 > T_1$: $arrow.double W_(S)(p) > 0$\ Leistungszahl $"COP" = (Q_(R_2))/(W_(S)) <= 1/(1 - T_1/T_2)$],
    cellx(colspan: 2)[Mit $f(x,y,z)=0, omega = omega(x, y)$ (also $x=x(y,z)$ etc.) gilt:
$eval(pdv(x,y))_z = eval(pdv(y,x))_z^(-1)$, 
$-1 = eval(pdv(x,y))_z eval(pdv(y,z))_x eval(pdv(z,x))_y$, 
$eval(pdv(x,omega))_z = eval(pdv(x,y))_z eval(pdv(y,omega))_z$, 
$eval(pdv(x,z))_omega = eval(pdv(x,y))_omega eval(pdv(y,z))_omega$, 
$eval(pdv(x,y))_z = eval(pdv(x,y))_omega + eval(pdv(x,omega))_y eval(pdv(omega,y))_z$],

)

#tablex(
    columns: (auto, auto),
//#thmbox(title: "1. Hauptsatz")[
cellx(colspan: 2, fill: green.lighten(60%))[*1. Hauptsatz*\ Für jedes $S in cal(S)$ gilt:
1. $forall sigma_1, sigma_2 in Sigma_S exists p in cal(P)_S: p text("verbindet") sigma_1 text("mit") sigma_2$
2. $forall p, p' in cal(P)_S text("mit gleichem Start und endzustand"):$ $W_(S)(p) = W_(S)(p')$
$arrow.double forall S, sigma in Sigma_S: exists "id"_S^sigma in cal(P)_S "und" W_(S)("id"_S^sigma) = 0$
$arrow.double text("falls") p in cal(P)_S text("rev."): W_(S)(p^"rev") = - W_(S)(p)$],
//],
//#thmbox(title: "Entropiesatz")[
cellx(colspan: 2, fill: green.lighten(60%))[*Entropiesatz*\ In einem adjabatischen Prozess kann die Entropie eines (abgeschlossenen?) Systems nicht abnehmen.\
$p in cal(P)$ adjabatisch auf $S$ $arrow.double$ $S_(S)(floor(p)_S) <= S_(S)(ceil(p)_S)$ und $"="$ falls $p$ rev.
],
//#thmbox(title: "2. Hauptsatz")[
cellx(colspan: 2, fill: green.lighten(60%))[*2. Hauptsatz*\ Sei $S, R in cal(S), R text("Reservoir"), S and R = emptyset$.
    $arrow.double forall p in cal(P)_(S or R) text("zyklisch auf ") S: W_(S)(p) >= 0$
    //#image("2terHS.png", width: 25%)
],
//#image("CarnotMaschine.png", width: 25%)
//#thmbox(title: "Carnots Theorem")[
cellx(colspan: 2, fill: green.lighten(60%))[*Carnots Theorem*\ Sei $(S, R_1, R_2, p)$ eine reversible Carnot-Maschine, $(S', R_1, R_2, p')$ eine Carnot-Maschine. OBDA $Q_(R_2)(p') > 0$.
    $arrow.double$\
    $-(Q_(R_1)(p'))/(Q_(R_2)(p')) <= -(Q_(R_1)(p))/(Q_(R_2)(p))$ und falls $p'$ rev., dann Gleichheit.
],
//#thmbox(title: "Clausius-Theorem")[
cellx(colspan: 2, fill: green.lighten(60%))[*Clausius-Theorem*\ Seien $S, {R_i}_i^N in cal(S)$. Seien ${p_i}_i^N in cal(P)_(S or R_i)$ mit $W_(R_i)(p_i) = 0$. $p = compose_i p_i text(" zykl. auf ") S$.\
    $arrow.double sum_i^N Q_S(p_i)/T_i <= 0$ mit Gleichheit falls $p$ rev. Falls quasistatisch dann $integral.cont (delta Q)/T <= 0$ mit Gleichheit falls $p$ rev.
],
cellx(colspan: 2, fill: white)[#underline("Entropie"): Sei $p = compose_i p_i$. #padeqbox($dd(S) = (delta Q)/T$) #padcondbox($eval(pdv(S_"max", U_(S_i))) = 0$)\ #padeqbox($S_(S)(sigma) := sum_(i=1)^N (Q_(S)(p_i))/(T_i) + S_"ref" eq.triple integral_(sigma_"ref")^(sigma) (delta Q_S)/T + S_"ref"$)\ #eqbox($Delta S(p' compose p) = Delta S(p') + Delta S(p)$) Konkav #eqbox($Delta S_(A or B) = Delta S_A + Delta S_B$) Homogen($S(lambda X) = lambda S(X)$) Supperadditiv($S(z_1 + z_2) >= S(z_1) + S(z_2)$)],
cellx(colspan: 2)[$Z_S$ #underline("homogen") Grad $k$: $Z_(lambda S)(lambda sigma) = lambda^k Z_(S)(sigma)$\ #underline("intensiv:") $T,P, k = 0$ #underline("extensiv:") $U,S,V,N, k = 1$],
[Extremalprinzipien: Bei Glg. $eval(F)_(V,T)^"min"$, $U^"min"$, $S^"max"$]

)

]
#pagebreak()
#columns(3, gutter: 0.25cm)[

#tablex(columns: (auto, auto), fill: purple.lighten(80%),
    cellx(colspan: 2)[*Legendre Transformation* ($A, D subset RR^n, f: D arrow RR$)],
    [$A$ #underline("konvex")], [$forall lambda in [0,1], forall x,y in A: lambda x + (1-lambda)y in A$],
    [$f$ #underline("konvex")], [$Gamma(f) = {(x,t) in D times RR: t >= f(x)}$ konvex. ($approx (f'')_"lok" > 0$)\ $arrow.double f(lambda x + (1-lambda)y) <= lambda f(x) + (1-lambda)f(y)$],
    [$f$ #underline("strikt kx")], [$f(lambda x + (1 - lambda)y) < lambda f(x) + (1-lambda)f(y)$],
    [$f$ #underline("konkav")], [$f(lambda x + (1 - lambda)y) >= lambda f(x) + (1-lambda)f(y)$],
    [#underline("Leg.TF") $f^*$], [$f^*(p) = sup_(x)[(p x - f(x))]$\ $f^*$ ist konvex und $f^(**) = f$ falls f konvex.\ $f^*(p,y)$ konkav in $y$ falls $f$ konv in $x,y$],
    cellx(rowspan: 3)[spez.\ $f: R arrow R$], [$f$ konv und $p_0 = f'(x_0)$ $arrow.double f^*(p_0) = p_0 x_0 - f(x_0)$],
    /* */ [$f$ konv und $C^1$ in $x_0$ $arrow.double p_0 = f'(x_0)$\ $arrow.double f^* in C^1 and (f^*)'(p_0) = x_0$],
    /* */ [$f$ strikt konv und $C^1$ $arrow.double f^(*)(p) = p x - f(x)$\ $x = (f')^(-1)(p)$, $(f*)' = (f')^(-1)$]
)

#tablex(columns: (auto, auto),
    [#underline("Wärmekap")], [#underline("isochor"): $C_V := eval((delta Q)/(diff T))_V = eval(pdv(U,T))_V$\ #underline("isobar"): $C_p := eval((delta Q)/(diff T))_p = eval(pdv(U, T))_p + p eval(pdv(V,T))_p$],
    [#underline("isoth. Kompressibilität")], [$kappa_T := -1/V eval(pdv(V,p))_T$],
    [#underline("Volumen-")\ #underline("ausdehnungskoeff.")], [$alpha := 1/V eval(pdv(V,T))_p$ $arrow.double C_p - C_V = (T V alpha^2)/(kappa_T)$],
    [#underline("Stabilitätsbedingungen")], [$C_p >= C_V >= 0, kappa_T >= 0$],
    [#underline("molare Wärmekap.")], [$c_x := C_x/n$, $n = N/N_A$],
    [#underline("Adiabatenexponent")], [$gamma := C_p/C_V$],
    [#underline("Adiabatische Wand")\ $Delta V arrow.double P' = P''$], [Lässt weder Wärme noch Teilchen durch. (Bewegl.)],
    [#underline("Diathermische Wand")], [$Delta T arrow.double Delta U arrow.double T' = T''$],
    [*Gibbssche Phasenregel*], [$f = k + 2 - n$, $k = text("#Komp"), n = text("#koexPh")$],
    [*Clausius-Clapeyron*], [Entlang Koex-Kurve zweier Phasen gilt: $pdv(p,T) = (S_2 - S_1)/(V_2 - V_1) = L_12/(T(V_2-V_1))$],
)
#tablex(columns: 1,
    cellx(fill: blue.lighten(60%))[*Modelle*],
    cellx(fill: blue.lighten(90%))[*Ideales Gas*
    #eqbox($delta W = -p dd(V)$)\
    #eqbox($p V = n R T$) #eqnametext("thZg")
    #eqbox($dd(U) = (n)C_V dd(T)$) #eqnametext("kalZg")\
    #padeqbox($C_V := eval(pdv(U,T))_V$) #padeqbox($eval(pdv(U,p))_T = 0$)
    #padeqbox($alpha = 1/T$) #padeqbox($kappa_T = 1/p$) #padeqbox($C_p - C_V = n R$) #padeqbox($gamma = (n R)/C_V + 1$)\
    #condbox($dd(U) = - p dd(V)$)#condtext("adia") #condbox($p V^gamma, T V^(gamma - 1), T^(gamma)p^(1- gamma) = "const"$)#condtext("adia")\
    #subbox()[*Thermalisierung* (Wärmeaustausch):
    $pdv(S, U_A) = 0 arrow.double T_F^A = T_F^B$,
    $Delta U_(A or B) = 0$ und $U_i = N_i C_V T_i$ $arrow.double C_(V)(N_(A)(T_F - T_A^"init") + N_(B)(T_F - T_B^"init")) = 0$
    $Delta S_(A)(T,V) = N_A (C_V log(T/T_0) + R log(V/V_0))$]
    ],
    cellx(fill: navy.lighten(90%))[*Isotrope paramagnetische Substanz*
    #eqbox($delta W = H dd(M)$)\
    #eqbox($K H = M T$) #eqnametext("thZg(Curie)")
    #eqbox($dd(U) = C_M dd(T)$) #eqnametext("kalZg")
    #padeqbox($C_M = eval(pdv(U,T))_(text("HM"))$)
    #padeqbox($eval(pdv(U,H))_T = 0$) #padeqbox($dd(U) = (C_M K)/M (-H/M dd(M) + dd(H))$)
    #subbox()[*Magnetische Carnot-Maschine* #eqbox($eta = eta_C$)
        #padcondbox($T = T_0 exp((M^2 - M_0^2)/(2 K C_M))$)#condtext("adjab") #condbox($W = integral H dd(M)$)#condtext("isoth.")
        ],
    ],
)

// START KLASSISCHE STATISTISCHE MECHANIK
#tablex(
    columns: (38%, 62%),
    fill: none,
    [Phasenraum], [$Gamma_N = RR^(6N)$ für $N$ Teilchen, $x=(q,p) in Gamma_N$ und $q = (q_1..q_n)$],
    [Wahrscheinlichkeits-\ mass auf $Gamma_N$], [$dd(mu)(x) = omega(x)dd(x)$\ $omega(x)$: Wahrscheinlichkeitsdichte],
    [Observable $f$], [$f: Gamma_N arrow RR$, $x arrow.bar f(x)$],
    [Erwartungswert], [$expval(f)_omega = integral dd(x) omega f$\ $expval(f)_(omega_t) = integral dd(x) omega(x)f(phi_(t)(x))$],
    [Entropie von $omega(x)$], [$S(omega) := -k_B integral dd(x) omega log(omega)$],
    [Zeitentwicklung\ ($H(x)$ ind. Fluss)], [$omega(x) = omega_(t=0)(x)$. $x arrow.bar phi_(t)(x)$. $omega_(t)(x) = omega(phi_(-t)(x))$],
    [Zeitmittelwert], [$1/T integral_0^T dd(t) expval(f)_(omega_t)$],
    [Thermodynamisches\ Gleichgew.], [$expval(f)_overline(omega) = lim_(T arrow infinity) 1/T integral_0^T dd(t) expval(f)_(omega_t)$\ wobei $overline(omega) := lim_(T arrow infinity) 1/T integral_0^T dd(t) omega_t$],
)
#tablex(
    columns: (auto, auto),
    cellx(colspan: 2, fill: green.lighten(60%))[*Ergodenhypothese* Fast alle Bahnen mit $E$ konstant besuchen fast alle Punkte in $Gamma_E$ mit gleicher Häufigkeit und immer wieder.\ Formell: $forall E, forall omega(x) eq.triple tilde(omega)(x)delta(H(x)-E): overline(omega) = omega_E$ und somit $expval(f)_overline(omega) = expval(f)_(omega_E)$],
    cellx(colspan: 2, fill: green.lighten(60%))[*Satz über Max. Entropie*: Die mikrokan. Gesamtheit $omega_(E)(x)$ maximiert für $E, N$ fest die Entropie.],
    cellx(colspan: 2, fill: green.lighten(60%))[*Gleichverteilungssatz*: $expval(x_i pdv(H,x_j))_(omega_E) = delta_(i j) k_B T$],
    cellx(colspan: 2)[*Mikrokanonisches Ensemble* ($S$ isoliert, Fix: $E, N, V$)],
    [#underline("Gesamtheit")], [$omega_(E)(x) = 1/Sigma delta(H(x) - E)$],
    [#underline("Zustandssumme")], [$Sigma(E,V,N) = integral_(Gamma_N)dd(x) delta(H(x) - E)$],
    [#underline("Entropie")], [$S(E,V,N) = k_B log(Sigma)$],
    cellx(colspan: 2)[*Kanonisches Ensemble* ($S, R$, Fix: $N, V$, Energieaustausch mit $R$)],
    [#underline("Gesamtheit")], [$omega_(beta)(x) = 1/Z exp(-beta H(x))$],
    [#underline("Zustandssumme")], [$Z(beta, V, N) = integral dd(x)e^(-beta H(x))$\ $= integral_RR dd(E)e^(-beta E)dot Sigma(E,V,N)$],
    [#underline("Freie Energie")], [$F(beta, V, N) = -k_B T log(Z)$],
    [#underline("Entropie")], [$S(beta, V, N) = (U - F)/T = k_B beta U + k_B log(Z)$],
    cellx(colspan: 2)[*Grosskanonisches Ensemble* ($S, R$, Fix: $V$)\ Energie- und Teilchenaustausch mit $R$],
    [#underline("Gesamtheit")], [$omega_(beta, mu)(N,x) = 1/Xi e^(-beta H(x) + beta mu N)$],
    [#underline("Zustandssumme")], [$Xi(beta, V, mu)$\ $=sum_(N=0)^infinity integral dd(x) e^(-beta H(x) + beta mu N)$\ $= sum_(N=0)^infinity z^N Z(beta,V,N)$\ $z = e^(beta mu), beta = 1/(k_B T)$],
    [#underline("Potential")], [$Omega(T,V,mu) = -k_B T log(Xi)$],
    [#underline("Teilchenzahl")], [$N = -pdv(Omega,mu)_(T,V)$],
    [#underline("Entropie")], [$S(T,V,N) = (U - Omega)/T$\ $= k_B beta (U - mu N) + k_B log(Xi)$],
)

    PH-Ü: 1.o: $dv(P,T) = (Delta S)/(Delta V)$ 2.o: $Delta S_j = Delta V_j = 0$ $Delta C_P = dv(P,T)dot V T Delta alpha$,
    #condbox($N = Sigma_i n_i$) #condbox($Sigma = (N!)/(product n_i!)$) #condbox($S = -k_B Sigma_i log(n_i/N)$) #condbox($U = Sigma_i epsilon_i n_i$) #condbox($n_i = A exp(-beta epsilon_i)$)

]
