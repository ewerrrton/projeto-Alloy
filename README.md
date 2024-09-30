# projeto-Alloy

// Definindo as entidades principais
sig Pessoa {
    	nome: one String
}

sig Professor extends Pessoa {
    	disciplinas: set Disciplina
}

sig Aluno extends Pessoa{}

sig Disciplina {
    	nome: one String
}

sig Laboratorio {
    	nome: one String
}

// Definindo os horários possíveis para reserva
abstract sig Horario {}

one sig Horario_8_10, Horario_10_12, Horario_14_16, Horario_16_18 extends Horario {}

// Definindo os dias úteis
abstract sig Dia {}

one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

// Definindo a Reserva
sig Reserva {
	Pessoa: one Pessoa,
    	laboratorio: one Laboratorio,
    	dia: one Dia,
    	horario: one Horario,
	disciplina: lone Disciplina //pois caso o aluno reserve, pode ser nenhum, e se for um professor havera uma disciplina relacionada
}

// Definindo a Lista de Espera
sig Espera {
   	pessoa: one Pessoa,
	laboratorio: one Laboratorio,
	dia: one Dia,
    	horario: one Horario
}

// Restrição para garantir que as reservas são sempre de duas horas
fact ReservasDuasHoras {
	all r: Reserva | r.horario in Horario_8_10 + Horario_10_12 + Horario_14_16 + Horario_16_18
}

// Garantir que cada professor tem exatamente dois horários por semana por disciplina
fact DoisHorariosPorDisciplina {
	all p: Professor, d: Disciplina | 
        	d in p.disciplinas => 
			#r: ((Reserva | r.professor = p and r.disciplina = d)) = 2
}


// Um professor pode ter várias disciplinas, logo mais de uma reserva de horários semanais
fact VariasDisciplinasPossiveis {
    	all p: Professor | 
        	#p.disciplinas >= 1
}

// Restrição para que nenhum laboratório tenha dois horários ocupados ao mesmo tempo
fact SemConflitoDeReservas {
    	all l: Laboratorio, d: Dia, h: Horario |
        	one r: Reserva | r.laboratorio = l and r.dia = d and r.horario = h
}

// Se o professor estiver na lista de espera para um horário, a disciplina não pode estar sendo usada em outro horário
fact EsperaSemUsoConflitante {
    	all e: Espera |
        	no r: Reserva | r.professor = e.professor and r.dia = e.dia and r.horario = e.horario
}

// Garantir que um pedido na lista de espera pode ser alocado em outro laboratório se houver disponibilidade
fact RealocaEsperaEmOutroLaboratorio {
    	all e: Espera |
        	some l: Laboratorio, d: Dia, h: Horario |
            	no r: Reserva | r.laboratorio = l and r.dia = d and r.horario = h =>
            	{e.laboratorio = l and e.dia = d and e.horario = h}
}

// Garantir que um professor na lista de espera pode sobrepor uma reserva de aluno
fact PrioridadeDisciplina {
    	all e: Espera |
        	e.pessoa in Professor => 
            	some r: Reserva | 
                	r.laboratorio = e.laboratorio and r.dia = e.dia and r.horario = e.horario and
                	r.pessoa in Aluno => {
                    	// Se um professor está na lista de espera e existe uma reserva de aluno, o professor pode sobrepor
                   	// Remover a reserva de aluno para permitir a reserva do professor
                    	e.laboratorio = r.laboratorio and e.dia = r.dia and e.horario = r.horario
                }
}

// Garantir que um professor não lecione a mesma disciplina no mesmo dia
fact SemDuplicacaoDeReservasPorDia {
    all p: Professor, d: Dia | 
        all r1: Reserva | 
            r1.professor = p and r1.dia = d =>
                // Não deve haver outra reserva para a mesma disciplina no mesmo dia
                no r2: Reserva | 
                    r2.professor = p and r2.disciplina = r1.disciplina and r2.dia = d
}




// Exemplo inicial de instâncias para testes
pred showExample {
    let lcc1 = Laboratorio {
        nome = "LCC1"
    }, lcc2 = Laboratorio {
        nome = "LCC2"
    } |
    some p: Professor | {
        some Reserva | professor = p and laboratorio = lcc1
    }
}

run showExample for 5 Professor, 5 Dia, 5 Horario, 2 Laboratorio
