# Atlas relacional de divisibilidade: Gram nativo e limites

## Resultado

O Gram nativo multibase é exatamente uma expressão em coordenadas de câmera
do kernel aritmético `K(d,e)=1/lcm(d,e)`, multiplicado pela sobreposição dos
níveis `min(cameraSlope b, cameraSlope c)`. A afirmação vale para quaisquer
duas câmeras suportadas, não apenas para as seis câmeras do certificado.
O fator de níveis permanece necessário: o kernel de divisibilidade sozinho
realiza a média dos perfis, não todo o Gram ponderado.

O módulo `NativeCarrySpectralWeyl/Finite/RelationalDivisibilityGram.lean`
identifica literalmente `periodicMeanKernel` e `gramKernel`. Não modifica
definições anteriores, normalizações ou pins. A síntese mantém todos os
produtos cruzados; o `Finsupp` reúne apenas resoluções iguais.

## Proveniência e auditoria inicial

Execução e verificação no servidor `ssh llm`. Checkouts encontrados:

| Repositório | Checkout | Estado consultado |
|---|---|---|
| native-carry-spectral-weyl | `/home/thlinux/native-carry-spectral-weyl` | branch inicial `agent/form-first-all-bases-camera-extension`, limpa, HEAD `2236bc5`; já integrada por PR #14; base atualizada para `248249ce098491f4194209d8e698dc5965f1405d` |
| genuine-zero-uniform-atlas-energy | `/home/thlinux/genuine-zero-uniform-atlas-energy` | main local `3d2031c96c90d9cd5afd002e9820d89aca3edd32`, desatualizada; crosswalk adicional consultado em `origin/main`, `2f5c38321d63752f891ef99622ff0685bc62c0ce` |
| carry-self-adjoint-operator | `/home/thlinux/carry-self-adjoint-operator` | `1645a7c`, com dois arquivos C2OddTfvdTransport preexistentes não rastreados, preservados |
| geometry-of-numbers | `/home/thlinux/geometry-of-numbers` | `e1084b43533255b399b82dc307b536d7dfdca07f`; instruções AGENTS consultadas; nenhum módulo portado |
| finite-native-carry-operator | `/home/thlinux/finite-native-carry-operator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` |

Weyl fixa Lean `v4.32.0`, GreenFrame
`cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`, FiniteNativeCarryOperator
`00e9d6beb17226545abf5ddf90bbfede6c7146b0` e Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. Os pins ficaram intactos.
O Atlas local fixa CPFormal `v0.62.0`; o autoadjunto fixa o crosswalk
`150cfc7fb08da96bf8117f15869cc2b819d593c2` e geometry-of-numbers
`d7cc54f5c485320f1fada33118e9e6101488819a`. Estes repositórios não foram
atualizados nem usados como novas dependências deste PR.

### Reutilização e hipóteses

| Fonte auditada | Declarações e obrigações relevantes |
|---|---|
| Camera/PeriodicProfiles | `profile`, `cameraSlope`, `dvdIndicator`; periodicidade para `2 ≤ b`; C2 tem slope 4; par retém `b/2` |
| Finite/Gram | `periodicProductMean`, `periodicGramMatrix_apply`; PSD por soma de rank-one e Schur; `sixCameraGram_eq`, `sixCameraGram_det`, `sixCameraGram_posDef` |
| Infinite/GramKernel | `CameraIndex={b // 2 ≤ b}`; `pairPeriod_pos`; média independente de múltiplo comum positivo; `finiteGramMatrix_posDef` e realização por quadrados em níveis/resíduos |
| Infinite/CameraCompletion | `inner_cameraVector` realiza o Gram oficial na completion existente |
| Infinite/Kolmogorov | `inner_kolmogorovVector` realiza a média dos perfis; completion sem assumir que esta média seja definida positiva |
| Infinite/Naimark | `inner_naimarkCameraVector`, `naimarkIsometry_inner`; realização do fator min por intervalos e isometria já existente |
| Finite/Whitening | `positiveInverseSqrt_whitens` requer Gram `PosDef`; nenhuma nova positividade foi assumida |
| Camera/FiniteCoefficientBridge | `finiteCoefficient` é seed mais soma dos brackets alinhados; fonte da reconstrução material |
| Limits/FiniteDefectCovariance | igualdade perfil/core exige posição positiva e suporte core; zero fora da janela; covariâncias normalizadas convergem; isso não é ainda uma estimativa de projetores |
| Atlas: EmpiricalCameraGeometry/Operator | seis períodos `4,3,4,5,6,7`; raios pares antipodais; prefixo mais tail no domínio de convergência `re(s)>-1` |
| Atlas: EmpiricalCameraHigherDerivativeCrosswalk | igualdade exata de radii, alignedCenter, seed e block com Weyl; consultada em origin/main porque ausente do checkout local |
| Atlas: EmpiricalStackProjection | conserva vetor câmera/tail/clock e a projeção transversal; não fornece igualdade com o projetor material deste atlas |
| Autoadjunto: FiniteEnrichedCameraState | projeção, complemento, Parseval e reconstrução exigem row Gram `PosDef` |
| Autoadjunto: FiniteNativeDepthRawCameraGram | Gram das linhas literais; convergência normalizada para sixCameraGram |
| Autoadjunto: FinitePhysicalSixCameraConcreteWhitening | row Gram literal `PosDef` para cutoff `M≥1`, certificado por minor; whitening literal já disponível |
| Autoadjunto: FiniteEnrichedCameraNaimarkEscapeIntertwining | `NaimarkProjectorIntertwiningSeam` exige dois quadrados, readout e síntese, num transporte tipado |
| Autoadjunto: CompletedNativeCameraVerticalHorizontalEnergyCrosswalk | resíduos de readout/síntese e embedding de energia explícitos; vanishing não é automático |

## Demonstração aritmética

Defina `e_d(n)=1` se `d ∣ n`, zero em caso contrário. A interseção é
`e_d e_e=e_lcm(d,e)`. Para `d>0`, exatamente um resíduo em `[0,d)` é
múltiplo de d: zero. Repetir esse bloco num período `L` divisível por d dá
`sum e_d=L/d`. Assim, para d,e,L positivos e d,e divisores de L,

`L⁻¹ sum(n<L) e_d(n)e_e(n)=1/lcm(d,e)`.

`divisibility_inner` é a prova exata no kernel. `divisibility_period_independent`
compara quaisquer dois períodos admissíveis. `divisibilityKernel_posSemidef`
escolhe o produto das resoluções de uma família finita, realiza cada entrada
como média de produtos e reutiliza a positividade da soma de rank-one.
Não introduz medida infinita. Resolução zero fica fora das hipóteses públicas
de realização/positividade.

## Perfis e fatoração

Os coeficientes de `profileCoefficients` são:

| Câmera | Resoluções | Coeficientes |
|---|---|---|
| 2 | 1,2,4 | 1,-1,-2 |
| ímpar | 1,b | 1,-b |
| par, b≥4 | 1,b/2,b | 1,1,-(b+2) |

`profile_finsupp` demonstra a igualdade com o perfil nativo.
`resolution_pos` e `resolution_dvd_slope` tornam a contagem aplicável a todos
os canais. `periodicProductMean_relational` expande a síntese completa,
permuta as somas finitas e aplica a identidade aritmética em cada produto.

`periodicMeanKernel_relational` usa o período MMC oficial dos slopes.
`gramKernel_relational` conserva o fator min dos níveis.
`gramKernel_finsupp` fornece a fórmula dupla em resoluções:

`G(b,c)=min(ell_b,ell_c) sum_d sum_e A_b(d) A_c(e) / lcm(d,e)`.

## Certificado das seis câmeras e geometria

`sixCamera_relational_certificate` identifica a fatoração com `sixCameraGram`
reutilizando o certificado periódico anterior. `relationalMeanRat_cast`
liga a construção racional à real. `sixCamera_relational_rational_certificate`
fecha as 36 entradas em ℚ, usando apenas os nove produtos de resoluções por
par de câmeras, sem enumerar novamente os 420 resíduos. A matriz, determinante
`4_981_760` e positividade definida anteriores são preservados.

`inner_cameraVector_relational` e `inner_naimarkCameraVector_relational`
reutilizam os espaços e a isometria existentes. A realização finita por
`Phi_b(j,n)=1_{j<ell_b} f_b(n)` já aparece no teorema
`finiteGramMatrix_quadratic_eq_sum_sq`; o peso da soma de resíduos é `1/L`.
Nenhum segundo espaço Hilbert foi construído.

A invariância `P_(SF)=P_F` para mudança invertível de coordenadas do mesmo
row space é um próximo lema de álgebra de projetores; não foi adicionado como
novo theorem neste PR. Não se conclui igualdade dos subespaços de famílias
arbitrárias a partir da identidade do kernel.

## Dinâmica: um no-go exato

`periodicSecondDifference` é `2I-T-T⁻¹` em `Fin 420`.
`secondDifference_c5_not_in_sixCamera_span` prova que sua aplicação ao perfil
C5 não pertence ao span dos seis perfis. Toda combinação desses perfis tem
valores iguais nos resíduos 1 e 13; a segunda diferença C5 tem valores 5 e 0.

Esta é uma prova Lean de não invariância no carrier periódico dos perfis.
Para o carrier de níveis/resíduos, o mesmo argumento na linha j=0 dá uma
obstrução: cada Phi tem valores iguais nessas duas posições nessa linha.
Esta extensão não foi registrada como novo theorem Lean neste PR.
Para a projeção ortogonal sobre o span finito de perfis, a não invariância
implica `(I-P)Delta_1P≠0`; essa consequência usa a interface usual do projetor,
que não foi construída novamente aqui. O PR não afirma vanishing do defeito.

O shift de resíduos não é o gerador material logarítmico, Green ou operador
de alturas. Nenhum entrelaçamento dinâmico entre esses carriers foi fechado.

## Bordo literal e próximo gate no autoadjunto

Escolha primeiro um carrier material comum: as posições positivas da janela
`finiteFamilyWindow M sixCamera`. Ponha `C_M` igual à matriz literal existente,
e `B_M(b,n)=f_b(n)` para `1≤n≤ell_b M`, zero fora desse core.
Então `E_M=C_M-B_M` é uma definição, não uma premissa de aproximação.

As identidades existentes de core, janela e endpoint reconstroem o candidato:
na linha b, E vale 1 nas posições `ell_b M+1,...,ell_b M+h_b`, zero nas demais,
com `h_2=1` e `h_b=floor(b/2)` para as outras câmeras. O endpoint par deve
usar `even_finiteCoefficient_endpoint`: seu valor literal é 1, enquanto o
perfil periódico nesse endpoint vale 2. Esquecer essa correção altera o bordo.

`scripts/audit_relational_boundary.py` reconstrói seed e todos os brackets
inteiros, incluindo antipodais, em vez de assumir a fórmula de E. Nos cutoffs
1 a 100 verifica exatamente C=B+E, suporte/unit entries do bordo e
`||E||_F²=1+1+2+2+3+3=12`. Trata-se de experimento finito exato, não de prova
Lean para todos os cutoffs. A promoção a theorem universal requer ligar a
fórmula unitária acima às identidades de janela/core no mesmo carrier.

O menor caminho para a estimativa de projetores é:

1. Registrar no autoadjunto B_M e E_M no tipo material de C_M, e provar a
   fórmula universal do bordo e sua norma.
2. Demonstrar um lower bound uniforme para o menor valor singular de
   `B_M/sqrt(M)` para M suficientemente grande, a partir da convergência de
   seu row Gram para o Gram nativo positivo definido. Convergência sem taxa
   fornece eventualmente um gap positivo; deve ser formalizada para B_M.
3. Aplicar um lema quantitativo de perturbação da projeção do row space,
   com erro `||E_M||/sqrt(M)`, para obter `O(M⁻¹/²)`.

A norma de Frobenius controla a norma de operador, mas esse controle sozinho
não implica proximidade dos projetores sem o gap singular. A estimativa não
está provada neste PR. O gate exato para comparar com o Naimark completado
continua sendo o par de quadrados de `NaimarkProjectorIntertwiningSeam`, com
embedding de estados e transporte de coordenadas identificados. Igualdade de
Gram ou whitening isolado não fecha esses quadrados.

## Verificação e fronteira de confiança

Comandos oficiais executados no llm, com `/home/thlinux/.elan/bin` no PATH:

```bash
lake exe cache get
lake build --wfail NativeCarrySpectralWeyl.Finite.RelationalDivisibilityGram
lake build --wfail NativeCarrySpectralWeyl
python3 scripts/check_registry.py
lake env lean NativeCarrySpectralWeyl/Audit.lean > /tmp/relational-axioms.log
python3 scripts/check_axiom_output.py /tmp/relational-axioms.log
python3 scripts/audit_relational_boundary.py
```

O módulo foi importado pelo root público. São 21 novos teoremas públicos,
todos registrados e incluídos em `#print axioms`; registro total 1364,
69 claims. O guard oficial rejeita `sorry`, `admit`, novos `axiom` e `unsafe`.
Os axiomas fundacionais admitidos pela auditoria são os padrões de Mathlib,
não novas premissas matemáticas. Não se exige footprint vazio desta camada
real/Hilbert. Builds com `--wfail` passaram; mensagens informativas antigas
de `ring` em outros módulos não são warnings.

As pontes Green/TFVD, HP, Hankel, positividade all-order e identificação de
alturas não fazem parte da conclusão. O resultado fechado é a identificação
estática relacional do Gram; a obstrução dinâmica foi conservada explicitamente.

## Publicação e bloqueio de integração

Formalização validada no commit `f83ad1ab388ad627595eec20dbd393d2cc300f4e`,
publicado em `origin/agent/relational-divisibility-gram` e no
[PR #15](https://github.com/thiagomassensini/native-carry-spectral-weyl/pull/15).
O [workflow do commit exato](https://github.com/thiagomassensini/native-carry-spectral-weyl/actions/runs/38032806186)
foi marcado como failure antes de iniciar qualquer step. A annotation oficial
do check `114157088567` diz: “The job was not started because your account is
locked due to a billing issue.” Isso não é uma falha Lean nem uma validação
remota bem-sucedida: nenhum runner chegou a executar o checkout.

O build completo, registro e os 1364 relatórios de axiomas passaram no llm.
A integração foi conservadoramente bloqueada; não houve merge, force push
ou mudança no `origin/main`, que permanece na base `248249c` observada.
Não foram criadas worktrees. A branch está vinculada ao PR e deve ser integrada
após resolver o bloqueio da conta e executar novamente a CI; não é uma branch
de trabalho esquecida. Os arquivos preexistentes do autoadjunto foram preservados.
