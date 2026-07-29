/*
 * Assinaturas base
 */

abstract sig TipoDeConteudo {}
one sig Filme, Serie, Documentario extends TipoDeConteudo {}

abstract sig ClassificacaoIndicativa {}
one sig Livre, ApenasAdolescentes, ApenasAdultos extends ClassificacaoIndicativa {}

// Básico < Plus < Premium
abstract sig Plano {}
one sig Basico, Plus, Premium extends Plano {}

some sig Conteudo {
    tipoDoConteudo: one TipoDeConteudo,
    classificacaoIndicativa: one ClassificacaoIndicativa,

    /*
     * Conteúdos podem ser exigir um tipo de plano mínimo para permitir o acesso.
     *
     * Básico = Sem exigências
     * Plus = Exige plano Plus ou Premium
     * Premium  = Exige plano Premium
     */
    planoMinimo: one Plano
}

some sig Usuario {
    planoAssinado: one Plano,
    perfisAssociados: set Perfil,
    perfisEmUso: set Perfil
}

some sig Perfil {
    contaAssociada: one Usuario,
    catalogoAcessivel: set Conteudo,
    estahAssistindo: set Conteudo
}

/*
 * Fatos e regras
 */

// Fato: todo perfil é associado a exatamente um usuário.
fact AssociacaoPerfil {
    all u : Usuario | perfisAssociadosCorretos[u]
}

// Fato: um usuário deve ter pelo menos um perfil associado.
fact UsuarioNaoVazio {
    all u : Usuario | some u.perfisAssociados
}

// Um perfil está associado ao usuário correto.
pred perfisAssociadosCorretos[u : Usuario] {
    u.perfisAssociados = u.~contaAssociada
}

// Fato: perfis em uso pertencem ao mesmo usuário.
fact AssociacaoPerfilEmUso {
    all u : Usuario | perfisEmUsoCorretos[u]
}

// Um perfil em uso está associado ao usuário correto.
pred perfisEmUsoCorretos[u : Usuario] {
    u.perfisEmUso in u.perfisAssociados
}

// Fato: apenas perfis ativos (isto é, que estão assistindo algo) acessam conteúdos.
fact AcesssoAtivo {
    all u : Usuario | perfisAtivos[u]
}

// Um perfil ativo está assistindo a algum conteúdo
pred perfisAtivos[u : Usuario] {
    all pf : u.perfisAssociados | perfilEstahEmUso[pf,u] 
}

// Um perfil está em uso por um usuário
pred perfilEstahEmUso[pf : Perfil, u : Usuario] {
    pf in u.perfisEmUso iff some pf.estahAssistindo
}

// Fato: perfis só podem assistir conteúdos acessíveis.
fact ApenasAcessosPossiveis {
    all pf : Perfil | perfilAssistindoConteudoAcessivel[pf]
}

// Um perfil está assistindo a conteúdos acessíveis
pred perfilAssistindoConteudoAcessivel[pf : Perfil] {
    pf.estahAssistindo in pf.catalogoAcessivel
}

// Fato: restrições numéricas do número de perfis acessando conteúdos por tipo de plano
// assinado.
fact LimitacoesNumericasPlanos {
    // Plano Básico: no máximo dois perfis simultâneos.
    // Plano Plus: no máximo quatro perfis simultâneos.
    // Plano Premium: sem limites de perfis.
    all u : Usuario | limitePerfisPorPlano[u]
}

//Testa se o número de perfis está dentro do limite permitido pelo plano assinado
pred limitePerfisPorPlano[u : Usuario] {
    (u.planoAssinado = Basico implies #u.perfisEmUso <= 2)
    and
    (u.planoAssinado = Plus implies #u.perfisEmUso <= 4)
}

// Garante que o catálogo acessível de cada perfil contenha exatamente os conteúdos permitidos
// pelo plano assinado pelo usuário associado ao perfil.
fact CatalogoCorreto {
    all p: Perfil | p.catalogoAcessivel = conteudosLiberados[p.contaAssociada.planoAssinado]
}

/*
 * Funções e predicados
 */

// Função que retorna o conjunto de conteudos liberados para determinado plano
fun conteudosLiberados[pf: Plano]: set Conteudo {
    { c: Conteudo | planoCompativel[pf, c] }
}

// Função que retorna o conjunto de usuários que tem o plano premium
fun usuariosPlanoPremium: set Usuario {
    { u : Usuario | u.planoAssinado = Premium }
}

// Função que retorna o conjunto de usuários que tem o plano básico
fun usuariosPlanoBasico: set Usuario {
    { u : Usuario | u.planoAssinado = Basico }
}

// Função que retorna o conjunto de usuários que tem o plano plus
fun usuariosPlanoPlus: set Usuario {
    { u : Usuario | u.planoAssinado = Plus }
}

// Um usuario pode assistir somente certo conteúdos.
pred planoCompativel[p : Plano, c : Conteudo] {
    c.planoMinimo = Basico
    or (p = Plus and c.planoMinimo != Premium)
    or p = Premium
}

/*
 * Asserts e testes
 */

// Verifica se a hierarquia de acesso entre os planos é respeitada todo conteúdo acessível pelo
// plano Básico também deve ser acessível pelo Plus, e todo conteúdo acessível pelo Plus também
// deve ser acessível pelo Premium.
assert HierarquiaDosPlanos {
    conteudosLiberados[Basico] in conteudosLiberados[Plus]
        and
    conteudosLiberados[Plus] in conteudosLiberados[Premium]
}

// Perfis associados a planos iguais devem possuir exatamente o mesmo catálogo acessível
assert MesmoPlanoMesmoCatalogo {
    all p1, p2: Perfil |
        p1.contaAssociada.planoAssinado = p2.contaAssociada.planoAssinado
            implies
        p1.catalogoAcessivel = p2.catalogoAcessivel
}

// A classificação indicativa não deve modificar as permissões de acesso.
assert ClassificacaoNaoInterfereNoAcesso {
    all p: Perfil |
        all c1, c2: Conteudo |

            c1.planoMinimo = c2.planoMinimo

            implies

            (
                c1 in p.catalogoAcessivel
                iff
                c2 in p.catalogoAcessivel
            )
}

// Conteudos basicos podem ser acessados por qualquer perfil
assert ConteudosBasicosLivresParaTodos {
    all p: Perfil |
        all c: Conteudo |
            c.planoMinimo = Basico
            implies
            c in p.catalogoAcessivel
}

// Um perfil que está assistindo a algo só pode estar associado ao seu usuário original
assert PerfilAssistindoAssociadoApenasAoUsuarioOriginal {
    all p: Perfil |
        some p.estahAssistindo
        implies
        (all u: Usuario | p in u.perfisEmUso implies u = p.contaAssociada)
}

// Conteúdos sendo assistidos precisam estar contidos no catálogo acessível pelo perfil
assert ConteudosAssistidosNoCatalogo {
    all p: Perfil | p.estahAssistindo in p.catalogoAcessivel
}

check HierarquiaDosPlanos for 5
check MesmoPlanoMesmoCatalogo for 5

check ClassificacaoNaoInterfereNoAcesso for 5

check ConteudosBasicosLivresParaTodos for 5

check PerfilAssistindoTemUsuario for 5
check PerfilAssistindoAssociadoApenasAoUsuarioOriginal for 5
check ConteudosAssistidosNoCatalogo for 5

run {} for 5
