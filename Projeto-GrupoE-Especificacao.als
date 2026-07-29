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

sig Conteudo {
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

sig Usuario {
    planoAssinado: one Plano,
    perfisAssociados: set Perfil,
    perfisEmUso: set Perfil
}

sig Perfil {
    contaAssociada: one Usuario,
    catalogoAcessivel: set Conteudo,
    estahAssistindo: set Conteudo
}

/*
 * Fatos e regras
 */

// Fato: plataforma não pode ser vazia.
fact PlataformaNaoVazia {
    some Conteudo
    some Usuario
    some Perfil
}

// Fato: todo perfil é associado a exatamente um usuário.
fact AssociacaoPerfil {
    all u : Usuario | u.perfisAssociados = u.~contaAssociada
}

// Fato: perfis em uso pertencem ao mesmo usuário.
fact AssociacaoPerfilEmUso {
    all u : Usuario | u.perfisEmUso in u.perfisAssociados
}

// Fato: apenas perfis ativos (isto é, que estão assistindo algo) acessam conteúdos.
fact AcesssoAtivo {
    all u : Usuario | all pf : u.perfisAssociados | pf in u.perfisEmUso iff some pf.estahAssistindo
}

// Fato: perfis só podem assistir conteúdos acessíveis.
fact ApenasAcessosPossiveis {
    all pf : Perfil | pf.estahAssistindo in pf.catalogoAcessivel
}

// Fato: restrições numéricas do número de perfis acessando conteúdos por tipo de plano assinado.
fact LimitacoesNumericasPlanos {

    // Plano Básico: no máximo dois perfis simultâneos.
    all u : Usuario | u.planoAssinado = Basico implies #u.perfisEmUso <= 2

    // Plano Plus: no máximo quatro perfis simultâneos.
    all u : Usuario | u.planoAssinado = Plus implies #u.perfisEmUso <= 4

    // Plano Premium: sem limites de perfis.
}

// Garante que o catálogo acessível de cada perfil contenha exatamente os conteúdos permitidos pelo plano assinado pelo usuário associado ao perfil.
fact CatalogoCorreto {
    all p: Perfil |
        p.catalogoAcessivel =
            conteudosLiberados[
                p.contaAssociada.planoAssinado
            ]
}

/*
 * Funções e predicados
 */

// Função que retorna o conjunto de conteudos liberados para determinado plano
fun conteudosLiberados[pl: Plano]: set Conteudo {
    {
        c: Conteudo |
            planoCompativel[pl, c]
    }
}

// Função que retorna o conjunto de usuários que tem o plano premium
fun usuariosPlanoPremium: set Usuario {
  {u : Usuario | u.planoAssinado = Premium}
}

// Função que retorna o conjunto de usuários que tem o plano básico
fun usuariosPlanoBasico: set Usuario {
  {u : Usuario | u.planoAssinado = Basico}
}

// Função que retorna o conjunto de usuários que tem o plano plus
fun usuariosPlanoPlus: set Usuario {
  {u : Usuario | u.planoAssinado = Plus}
}

// Testa se um usuario pode assistir certo conteudo
pred planoCompativel[p : Plano, c : Conteudo] {
  c.planoMinimo = Basico
  or (p = Plus and c.planoMinimo != Premium)
  or p = Premium
}

// Define um cenário específico para testar. Neste cenário, um usuário
// do plano Básico possui três perfis,apenas dois deles estão em uso,
// e um perfil assiste a dois conteúdos simultaneamente.
pred CenarioExemplo {
    some u: Usuario | {

        u.planoAssinado = Basico

        // O usuário possui três perfis cadastrados.
        #u.perfisAssociados = 3

        // Somente dois perfis estão em uso.
        #u.perfisEmUso = 2

        // Existem dois conteúdos básicos distintos.
        some disj c1, c2: Conteudo | {

            c1.planoMinimo = Basico
            c2.planoMinimo = Basico

            // Um perfil está assistindo aos dois conteúdos.
            some p: u.perfisEmUso |
                c1 + c2 in p.estahAssistindo
        }
    }
}

/*
 * Asserts e testes
 */

// Verifica se a hierarquia de acesso entre os planos é respeitada
// todo conteúdo acessível pelo plano Básico também deve ser acessível
// pelo Plus, e todo conteúdo acessível pelo Plus também deve ser acessível
// pelo Premium.
assert HierarquiaDosPlanos {
    conteudosLiberados[Basico] in conteudosLiberados[Plus]
    and
    conteudosLiberados[Plus] in conteudosLiberados[Premium]
}

// Perfis associados a planos iguais devem possuir exatamente o mesmo catálogo acessível
assert MesmoPlanoMesmoCatalogo {
    all p1, p2: Perfil |
        p1.contaAssociada.planoAssinado =
        p2.contaAssociada.planoAssinado

        implies

        p1.catalogoAcessivel =
        p2.catalogoAcessivel
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

// Um perfil que está assistindo a algo tem que ter um usuário associado
assert PerfilAssistindoTemUsuario {
    all p: Perfil |
        some p.estahAssistindo
        implies
        some p.contaAssociada
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
    all p: Perfil |
        p.estahAssistindo in p.catalogoAcessivel
}

check HierarquiaDosPlanos for 5
check MesmoPlanoMesmoCatalogo for 5

check ClassificacaoNaoInterfereNoAcesso for 5

check ConteudosBasicosLivresParaTodos for 5

check PerfilAssistindoTemUsuario for 5
check PerfilAssistindoAssociadoApenasAoUsuarioOriginal for 5
check ConteudosAssistidosNoCatalogo for 5

run {} for 5
