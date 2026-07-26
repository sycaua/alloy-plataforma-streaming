module plataforma

one sig plataforma {
    conteudos: set Conteudo,
    usuarios: set Usuario,
    perfis: set Perfil
}

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
    perfisAssociados: set Perfil
}

sig Perfil {
    contaAssociada: one Usuario,
    catalogoAcessivel: set Conteudo
}

// Fato: uma única plataforma para todos os componentes.
fact PlataformaUnica {
    all c : Conteudo | one p : plataforma | c in p.conteudos

    all u : Usuario |
        one p : plataforma | u in p.usuarios

    all pf : Perfil |
        one p : plataforma | pf in p.perfis
}

// Fato: todo perfil é associado a exatamente um usuário.
fact AssociacaoPerfil {
    all u : Usuario | u.perfisAssociados = u.~contaAssociada
}

// Fato: restrições numéricas dos números de perfis permitidos por tipo de plano assinado.
fact LimitacoesNumericasPlanos {

    // Plano Básico: no máximo dois perfis simultâneos.
    all u : Usuario |
        u.planoAssinado = Basico implies #u.perfisAssociados <= 2

    // Plano Plus: no máximo quatro perfis simultâneos.
    all u : Usuario | u.planoAssinado = Plus implies #u.perfisAssociados <= 4

    // Plano Premium: sem limites de perfis.
    all u : Usuario | u.planoAssinado = Premium implies #u.perfisAssociados >= 0
}

// Fato: o acesso aos conteúdos é definido pelo tipo de plano do usuário.
fact LimitacoesDeAcessoPlanos {

    // Plano Básico só libera acesso aos conteúdos básicos.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Basico implies 
        all c : pf.catalogoAcessivel | c.planoMinimo = Basico

    // Plano Plus libera acesso aos conteúdos básicos e aos pluses, mas não aos premiums.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Plus implies
            all c : pf.catalogoAcessivel | c.planoMinimo != Premium

    // Plano Premium libera acesso a todos os conteúdos.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Premium implies
            all c : pf.catalogoAcessivel | c.planoMinimo in Plano
}

assert BasicoAcessaApenasBasico {
    no pf : Perfil | pf.contaAssociada.planoAssinado = Basico and
        some c : pf.catalogoAcessivel | c.planoMinimo != Basico
}

assert PremiumAcessaApenasPlus {
    no pf : Perfil | pf.contaAssociada.planoAssinado = Plus and
        some c : pf.catalogoAcessivel | c.planoMinimo = Premium
}


assert TamanhoMaximoBasico {
    no u : Usuario | u.planoAssinado = Basico and #u.perfisAssociados > 2
}

assert TamanhoMaximoPlus {
    no u : Usuario | u.planoAssinado = Plus and #u.perfisAssociados > 4
}

assert PlataformaVazia {
    no p : Plataforma | #p.conteudos = 0 and #p.usuarios = 0 and #p.perfis = 0
} 

assert 

run {} for 5
