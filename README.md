# projeto-Alloy


// Definindo as entidades principais
sig Pessoa {}

sig Professor extends Pessoa {
    	disciplinas: set Disciplina
}

sig Aluno extends Pessoa {}

sig Disciplina {
	horarios: set Horario,
} {
	#horarios = 2  // Garante que cada disciplina tem exatamente 2 horários em dias diferentes
}

// Definindo o laboratório
sig Laboratorio {}

one sig LCC1, LCC2 extends Laboratorio{}

// Definindo os horários possíveis para reserva
abstract sig Horario {
	dia: one Dia,
	hora: one Hora 
}

abstract sig Hora {}

one sig Horario_8_10, Horario_10_12, Horario_14_16, Horario_16_18 extends Hora {}

// Definindo os dias úteis
abstract sig Dia {}

one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

// Definindo a reserva diretamente, sem expor a solicitação de sala
sig Reserva {
    	pessoa: one Pessoa,
    	laboratorio: one Laboratorio,
    	horario1: one Horario,
	horario2: one Horario,
	disciplina: lone Disciplina
}

// Definindo a lista de espera diretamente
sig ListaDeEspera {
    	pessoa: one Pessoa,
    	laboratorio: one Laboratorio,
    	horario1: one Horario,
	horario2: one Horario
}
// Predicado para verificar se a pessoa é um professor
pred isProfessor[p: Pessoa] {
    	p in Professor
}

// Predicado para verificar se a pessoa é um aluno
pred isAluno[p: Pessoa] {
    	p in Aluno
}

// Predicado para verificar se dois horários são iguais
pred horariosIguais[r1: Reserva, r2: Reserva] {
    r1.horario1 = r2.horario1 or r1.horario1 = r2.horario2 or
    r1.horario2 = r2.horario1 or r1.horario2 = r2.horario2
}

//Predicado que compara se 2 laboratórios são iguais
pred mesmoLaboratorio[r1: Reserva, r2: Reserva] {
	r1.laboratorio = r2.laboratorio
}

// Aluno nao tem disciplina
fact {
	all r: Reserva |
		isAluno[r.pessoa] => r.disciplina = none
}	

// Fato para garantir que toda entidade pessoa é professor ou aluno
fact {
 	all p: Pessoa | p in Aluno or p in Professor
}

// Todo laboratorio é LCC1 ou LCC2
fact {
 	all l:Laboratorio | l in LCC1 or l in LCC2
}
// Fato para garantir que toda pessoa esta na reserva ou lista de espera
fact {
    all p: Pessoa | 
        (some r: Reserva | r.pessoa = p) or 
        (some l: ListaDeEspera | l.pessoa = p)
}

// Fato para garantir que um prof lecionando varias disciplinas nao de choque de horario
fact {
	all p: Professor, d1: Disciplina, d2: Disciplina | 
       	(d1 != d2 and d1 in p.disciplinas and d2 in p.disciplinas) =>
		no (d1.horarios & d2.horarios)
}

// Fato para garantir que alunos so possuem 1 horario
fact {
    	all r: Reserva | 
        	isAluno[r.pessoa] => 
        	(r.horario1.dia = r.horario2.dia)
    	all l: ListaDeEspera | 
        	isAluno[l.pessoa] => 
        	(l.horario1.dia = l.horario2.dia)
}

// Fato para garantir que professores têm prioridade sobre alunos na reserva de sala
fact prioridadeProfessor {
    all rAluno: Reserva, rProf: Reserva |
        isAluno[rAluno.pessoa] and isProfessor[rProf.pessoa] and
        mesmoLaboratorio[rAluno, rProf] and horariosIguais[rAluno, rProf] =>
        some l: ListaDeEspera | l.pessoa = rAluno.pessoa and
	 l.laboratorio = rAluno.laboratorio and
	 l.horario1 = rAluno.horario1 and l.horario2 = rAluno.horario2
}

fact {
	all r1: Reserva, r2: Reserva |
	r1 != r2 =>
	not(horariosIguais[r1, r2] and mesmoLaboratorio[r1, r2])
}

// Predicado para verificar se há conflitos de reservas
pred noConflict {
    all r1, r2: Reserva | 
        r1 != r2 => 
        (r1.laboratorio != r2.laboratorio or r1.horario1 != r2.horario1 and r1.horario2 != r2.horario2)
}

// Adicionando a restrição ao modelo
fact {
    noConflict
}

// Predicado para verificar se uma pessoa não está em mais de um lugar ao mesmo tempo
pred semReservaDupla {
    all p: Pessoa, h: Horario | 
        lone r: Reserva | 
        r.pessoa = p and (r.horario1 = h or r.horario2 = h)
}

// Adicionando a restrição ao modelo
fact {
    semReservaDupla
}

// Todo professor leciona no minimo 1 disciplina
fact {
    	all p: Professor |
	#p.disciplinas >=1
}

fact {
	some Reserva
}

	
// A seguir estao alguns asserts para verificações básicas

// Assert para verificar se todos os professores têm pelo menos uma disciplina
assert ProfessoresTemDisciplinas {
    all p: Professor | #p.disciplinas >= 1
}
check ProfessoresTemDisciplinas

// Assert para verificar se não há conflitos de horários para reservas no mesmo laboratório
assert SemConflitoDeHorarios {
    no r1, r2: Reserva | 
        r1 != r2 and 
        r1.laboratorio = r2.laboratorio and 
        (r1.horario1 = r2.horario1 or r1.horario1 = r2.horario2 or 
         r1.horario2 = r2.horario1 or r1.horario2 = r2.horario2)
}
check SemConflitoDeHorarios

// Assert para verificar se alunos têm apenas um horário por dia
assert AlunosComUmHorarioPorDia {
    all r: Reserva | 
        isAluno[r.pessoa] => 
        r.horario1.dia = r.horario2.dia
}
check AlunosComUmHorarioPorDia

// Assert para verificar se uma pessoa não está em mais de um lugar ao mesmo tempo
assert SemReservaDupla {
    all p: Pessoa, h: Horario | 
        lone r: Reserva | 
        r.pessoa = p and (r.horario1 = h or r.horario2 = h)
}
check SemReservaDupla

// Assert para verificar se alunos não têm disciplinas atribuídas
assert AlunosSemDisciplinas {
    all r: Reserva | 
        isAluno[r.pessoa] => 
        r.disciplina = none
}
check AlunosSemDisciplinas

//Assert para verificar se os Profs tem prioridade sobre os alunos
assert prioridadeProfessorAssert {
    all rAluno: Reserva, rProf: Reserva |
        isAluno[rAluno.pessoa] and isProfessor[rProf.pessoa] and
        mesmoLaboratorio[rAluno, rProf]
	 and horariosIguais[rAluno, rProf] =>
        some l: ListaDeEspera | l.pessoa = rAluno.pessoa and
	 l.laboratorio = rAluno.laboratorio and l.horario1 = rAluno.horario1 and
	 l.horario2 = rAluno.horario2
}

check prioridadeProfessorAssert
