/*
 * Assinaturas base
 */

abstract sig TipoDeConteudo {}
one sig Documentario, Filme, Serie extends TipoDeConteudo {}

abstract sig ClassificacaoIndicativa {}
lone sig ApenasAdolescentes, ApenasAdultos, Livre extends ClassificacaoIndicativa {}

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
    perfisEmUso: some Perfil
}

some sig Perfil {
    contaAssociada: one Usuario,
    estahAssistindo: lone Conteudo
}

/*
 * Fatos e regras
 */

// Fato: perfis em uso pertencem ao mesmo usuário.
fact AssociacaoPerfilEmUso {
    all u : Usuario | u.perfisEmUso in u.~contaAssociada
}

// Fato: apenas perfis ativos (isto é, que estão assistindo algo) acessam conteúdos.
fact AcesssoSomenteAtivo {
    all pf : Perfil | (pf in pf.contaAssociada.perfisEmUso) iff some pf.estahAssistindo
}

// Fato: perfis só podem assistir conteúdos acessíveis.
fact ApenasAcessosPossiveis {
    all pf : Perfil | pf.estahAssistindo in conteudosAcessiveis[pf]
}

// Observação do cliente: toda classificação indicativa existente deve ter pelo menos um conteúdo associado a ela.
fact ClassificacoesIndicativasNaoIsoladas {
    all cl : ClassificacaoIndicativa | some classificacaoIndicativa.cl
}

// Fato: restrições numéricas do número de perfis acessando conteúdos por tipo de plano assinado.
fact LimitacoesNumericasPlanos {
    all u : Usuario |
        // Plano Básico: no máximo dois perfis simultâneos.
        (u.planoAssinado = Basico implies #u.perfisEmUso <= 2)
            and
        // Plano Plus: no máximo quatro perfis simultâneos.
        (u.planoAssinado = Plus implies #u.perfisEmUso <= 4)

        // Plano Premium: sem limites de perfis.
}

/*
 * Funções e predicados
 */

// Função que retorna todos os conteúdos que podem ser acessados por um dado perfil (considerando o plano do seu usuário).
fun conteudosAcessiveis[pf : Perfil] : set Conteudo {
    conteudosLiberados[pf.contaAssociada.planoAssinado]
}

// Função que retorna o conjunto de conteúdos que estão liberados para determinado plano.
fun conteudosLiberados[pl : Plano]: set Conteudo {
    { c : Conteudo | planoCompativel[pl, c] }
}

// Predicado que verifica se conteúdo pode ser acessado por um dado plano.
pred planoCompativel[pl : Plano, c : Conteudo] {
    c.planoMinimo = Basico or (pl = Plus and c.planoMinimo = Plus) or pl = Premium
}

/*
 * Asserts e testes
 */

// Verifica se a hierarquia de acesso entre os planos é respeitada por todo conteúdo acessível.
assert HierarquiaDosPlanos {
    conteudosLiberados[Basico] in conteudosLiberados[Plus]
        and
    conteudosLiberados[Plus] in conteudosLiberados[Premium]
}

// Perfis associados a planos iguais devem possuir exatamente o mesmo catálogo acessível.
assert MesmoPlanoMesmoCatalogo {
    all pf1, pf2 : Perfil |
        pf1.contaAssociada.planoAssinado = pf2.contaAssociada.planoAssinado
            implies
        conteudosAcessiveis[pf1] = conteudosAcessiveis[pf2]
}

// A classificação indicativa não deve modificar as permissões de acesso de um conteúdo.
assert ClassificacaoNaoInterfereNoAcesso {
    all pf : Perfil | all c1, c2 : Conteudo |
        c1.planoMinimo = c2.planoMinimo
            implies
        (c1 in conteudosAcessiveis[pf] iff c2 in conteudosAcessiveis[pf])
}

// Conteudos básicos podem ser acessados por qualquer perfil.
assert ConteudosBasicosLivresParaTodos {
    all pf : Perfil | all c : Conteudo |
        c.planoMinimo = Basico
            implies
        c in conteudosAcessiveis[pf]
}

// Um perfil que está assistindo a algo tem que estar associado a um usuário.
assert PerfilAssistindoAssociado {
    all pf : Perfil | some pf.estahAssistindo implies some pf.contaAssociada
}

// Um perfil que está assistindo a algo só pode estar associado ao seu usuário original.
assert PerfilAssistindoAssociadoAOriginal {
    all pf : Perfil | some pf.estahAssistindo
        implies
    (all u : Usuario | pf in u.perfisEmUso implies u = pf.contaAssociada)
}

// Conteúdos sendo assistidos precisam estar contidos no catálogo acessível pelo perfil.
assert ConteudosAssistidosNoCatalogo {
    all pf : Perfil | pf.estahAssistindo in conteudosAcessiveis[pf]
}

// Cenário exemplo que emprega todas os componentes da plataforma: usuários básico, plus e premium, perfis estáticos e em uso, todas as classificações indicativas e todos os tipos de conteúdo.
pred CenarioExemplo {
    #Usuario = 3
    one u1 : Usuario | u1.planoAssinado = Basico
    one u2 : Usuario | u2.planoAssinado = Plus
    one u3 : Usuario | u3.planoAssinado = Premium

    #Perfil = 5
    let
        u1 = { u : Usuario | u.planoAssinado = Basico },
        u2 = { u : Usuario | u.planoAssinado = Plus },
        u3 = { u : Usuario | u.planoAssinado = Premium }
    | {
        // Usuário 1 (básico) tem dois perfis
        #u1.~contaAssociada = 2
        // Usuário 2 (plus) tem dois perfis
        #u2.~contaAssociada = 2
        // Usuário 3 (premium) tem um perfil
        #u3.~contaAssociada = 1
    }

    #Conteudo = 5
    some c : Conteudo | c.classificacaoIndicativa = ApenasAdolescentes
    some c : Conteudo | c.classificacaoIndicativa = ApenasAdultos
    some c : Conteudo | c.classificacaoIndicativa = Livre

    some c : Conteudo | c.tipoDoConteudo = Documentario
    some c : Conteudo | c.tipoDoConteudo = Filme
    some c : Conteudo | c.tipoDoConteudo = Serie

    // Dois conteúdos básicos
    # { c : Conteudo | c.planoMinimo = Basico } = 2
    // Dois conteúdos plus 
    # { c : Conteudo | c.planoMinimo = Plus } = 2
    // Um conteúdo premium
    # { c : Conteudo | c.planoMinimo = Premium } = 1

    // Quatro perfis em uso
    # { pf : Perfil | some pf.estahAssistindo } = 4

    // Usuário 1 tem os dois perfis ativos
    one u1 : Usuario | u1.planoAssinado = Basico and #u1.perfisEmUso = 2
    // Usuário 2 tem apenas um dos dois perfis em uso
    one u2 : Usuario | u2.planoAssinado = Plus and #u2.perfisEmUso = 1
    // Usuário 3 está usando seu perfil.
    one u3 : Usuario | u3.planoAssinado = Premium and #u3.perfisEmUso = 1
}

run CenarioExemplo for 5
// run {} for 5
