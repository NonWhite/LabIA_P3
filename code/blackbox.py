import sys
import collections
from utils import *
from solver import Solver
from copy import deepcopy as copy

VAR_DELIMITER = '_'
DEBUG = False

class Blackbox( Solver ) :
	def preprocess( self ) :
		# Add maintaining actions for predicates
		states = [ True , False ]
		notident = [ '' , 'not_' ]
		for prop in self.predicates :
			for i in range( len( states ) ) :
				self.actions.append( {
					'precondition' : [ { 'state' : states[ i ] , 'name' : prop } ] ,
					'name' : 'maintain_%s%s' % ( notident[ i ] , prop ) ,
					'persistence' : [] ,
					'effect' : [ { 'state' : states[ i ] , 'name' : prop } ]
				} )
		self.total = len( self.predicates ) + len( self.actions )
		# Put propositions that are true in array
		self.nodes = {}
		for prop in self.start :
			prop[ 'time' ] = 0
			prop[ 'isaction' ] = False
			self.nodes[ self.getID( prop ) ] = prop
		self.graph = {}
		# Addding literal mutex inconsistence
		for litid in self.nodes :
			if -litid in self.nodes :
				if litid not in self.graph : self.graph[ litid ] = []
				self.graph[ litid ].append( -litid )
		# Add relations between actions (preconditions and effects)
		for act in self.actions : act[ 'previous' ] = []
		for act1 in self.actions :
			pred1 = act1[ 'precondition' ]
			for p in pred1 :
				resp = []
				for i in range( len( self.actions ) ) :
					eff2 = self.actions[ i ][ 'effect' ]
					if p in eff2 : resp.append( i )
				if len( resp ) > 0 : act1[ 'previous' ].append( resp )
		self.endpreconditions = []
		for g in self.goal :
			resp = []
			for i in range( len( self.actions ) ) :
				effect = self.actions[ i ][ 'effect' ]
				if g in effect : resp.append( i )
			if len( resp ) > 0 : self.endpreconditions.append( resp )
		#self.debug()

	def getID( self , prop ) :
		if prop == None : return ''
		time = prop[ 'time' ]
		pos = 0
		if prop[ 'isaction' ] :
			pos = getAllValues( self.actions , 'name' ).index( prop[ 'name' ] )
			pos += self.idactions
		else :
			pos = self.predicates.index( prop[ 'name' ] )
			pos += self.idpredicates
		ID = pos + time * self.total
		if not prop[ 'state' ] : ID = -ID
		return ID
	
	def getProposition( self , ID ) :
		isnegation = False
		if ID < 0 :
			isnegation = True
			ID = -ID
		pos = ( ID % self.total ) - 1
		resp = ''
		if pos >= len( self.predicates ) :
			pos -= len( self.predicates )
			resp = self.actions[ pos ][ 'name' ]
		else :
			resp = self.predicates[ pos ]
		resp = ( "~" if isnegation else "" ) + resp
		return resp

	def addAction( self ) :
		currentActs = []
		allIdPreds = []
		newnode = { 'mutex' : [] , 'links' : [] }
		preactions = {}
		for act in self.actions :
			ispossible = True
			lstPreds = []
			idPreds = []
			# Check preconditions
			for pred in act[ 'precondition' ] :
				prop = formProposition( pred[ 'name' ] , pred[ 'state' ] , self.steps , False )
				predID = self.getID( prop )
				ispossible &= ( predID in self.nodes )
				prop[ 'ID' ] = predID
				lstPreds.append( prop )
				idPreds.append( predID )
			# If all preconditions exists
			if ispossible :
				prop = formProposition( act[ 'name' ] , True , self.steps , True )
				prop[ 'previous' ] = act[ 'previous' ]
				self.nodes[ self.getID( prop ) ] = prop
				actID = self.getID( prop )
				currentActs.append( actID )
				allIdPreds.append( idPreds )
				# Link preconditions with action
				for pred in lstPreds :
					if pred[ 'ID' ] not in self.graph : self.graph[ pred[ 'ID' ] ] = copy( newnode )
					self.graph[ pred[ 'ID' ] ][ 'links' ].append( actID )
				# Link action with its effects
				if actID not in self.graph : self.graph[ actID ] = copy( newnode )
				lstEffects = []
				for eff in act[ 'effect' ] : lstEffects.append( formProposition( eff[ 'name' ] , eff[ 'state' ] , self.steps + 1 , False ) )
				for eff in lstEffects :
					effID = self.getID( eff )
					self.nodes[ effID ] = eff
					if effID not in preactions : preactions[ effID ] = []
					preactions[ effID ].append( actID )
					self.graph[ actID ][ 'links' ].append( effID )
		# Adding action mutex relations
		for i in range( len( currentActs ) ) :
			act1 = currentActs[ i ]
			preconditions1 = allIdPreds[ i ]
			for j in range( len( currentActs ) ) :
				if i == j : continue
				act2 = currentActs[ j ]
				preconditions2 = allIdPreds[ j ]
				if act2 in self.graph[ act1 ][ 'mutex' ] : continue
				# Action Mutex inconsistence
				for effid in self.graph[ act2 ][ 'links' ] :
					if -effid in self.graph[ act1 ][ 'links' ] :
						self.graph[ act1 ][ 'mutex' ].append( act2 )
						break
				if act2 in self.graph[ act1 ][ 'mutex' ] : continue
				# Action Mutex interference
				for effid in self.graph[ act2 ][ 'links' ] :
					newid = effid * ( -1 if effid < 0 else 1 ) - self.total
					newid = newid * ( 1 if effid < 0 else -1 )
					if newid in preconditions1 :
						self.graph[ act1 ][ 'mutex' ].append( act2 )
						break
				if act2 in self.graph[ act1 ][ 'mutex' ] : continue
				# Action Mutex necessity: Have preconditions with mutex
				for pre1 in preconditions2 :
					if act2 in self.graph[ act1 ][ 'mutex' ] : break
					for pre2 in preconditions1 :
						if pre1 in self.graph[ pre2 ][ 'mutex' ] :
							self.graph[ act1 ][ 'mutex' ].append( act2 )
							break
		# Literal Mutex in new level
		self.steps += 1
		start = self.steps * self.total + 1
		end = start + len( self.predicates )
		# Negation of literals
		for litid in range( start , end ) :
			if litid not in self.nodes : continue
			if -litid in self.nodes :
				if litid not in self.graph : self.graph[ litid ] = copy( newnode )
				self.graph[ litid ][ 'mutex' ].append( -litid )
				if -litid not in self.graph : self.graph[ -litid ] = copy( newnode )
				self.graph[ -litid ][ 'mutex' ].append( litid )
		# All ways are insatisfiable
		for ef1 in preactions :
			for ef2 in preactions :
				if ef1 == ef2 : continue
				if ef2 in self.graph[ ef1 ][ 'mutex' ] : continue
				act1 = preactions[ ef1 ]
				act2 = preactions[ ef2 ]
				needmutex = True
				for x in act1 :
					for y in act2 :
						if x == y : needmutex = False # Come from same action
						needmutex &= ( x in self.graph[ y ][ 'mutex' ] )
				if needmutex :
					if ef1 not in self.graph : self.graph[ ef1 ] = copy( newnode )
					self.graph[ ef1 ][ 'mutex' ].append( ef2 )
		self.printgraphrelations()
	
	def standarize( self , goal , clauses ) :
		impl = copy( goal )
		impl.extend( clauses )
		var = []
		for x in impl : var.extend( [ abs( int( r ) ) for r in x ] )
		var = list( collections.Counter( var ) )
		numvars = len( var )
		positions = {}
		for val in enumerate( var ) :
			positions[ val[ 1 ] ] = val[ 0 ] + 1
			positions[ -val[ 1 ] ] = -val[ 0 ] - 1
		self.translator = {}
		for ( key , value ) in positions.iteritems() : self.translator[ value ] = key
		for i in range( len( impl ) ) :
			for j in range( len( impl[ i ] ) ) :
				impl[ i ][ j ] = str( positions[ int( impl[ i ][ j ] ) ] )
		return ( numvars , impl )

	def getPreconditionActions( self , actionID , isGoalAction = False ) :
		lstPreds = []
		prop = ( None if isGoalAction else self.nodes[ actionID ] )
		if prop and prop[ 'time' ] < 1 : return []
		previous = ( self.endpreconditions if isGoalAction else prop[ 'previous' ]	)
		dec = ( 0 if not isGoalAction else 1 )
		for prearray in previous :
			resp = []
			for idx in prearray :
				p = self.actions[ idx ]
				prop = formProposition( p[ 'name' ] , True , self.steps - dec , True )
				if self.getID( prop ) not in self.nodes : continue
				resp.append( prop )
			lstPreds.append( resp )
		for i in range( len( lstPreds ) ) :
			lstPreds[ i ] = [ str( self.getID( x ) ) for x in lstPreds[ i ] ]
		return lstPreds

	def getPreactionClauses( self , actionID , isGoalAction = False ) :
		clauses = []
		lstPreAct = self.getPreconditionActions( actionID , isGoalAction )
		# Clause for goal action
		if isGoalAction : clauses.append( [ str( actionID ) ] )
		# Clauses type 1: Action preconditions
		for prev in lstPreAct :
			rule = [ str( -actionID ) ]
			for x in prev : rule.append( str( x ) )
			if len( rule ) > 1 : clauses.append( rule )
		# Clauses type 2: Only one of the actions per precondition
		for prev in lstPreAct :
			cl = []
			for x in prev : cl.append( "-%s" % x )
			if len( cl ) > 1 : clauses.append( cl )
		# Clauses type 3: Mutex of actions for preconditions
		for prev in lstPreAct :
			for x in prev :
				if int( x ) not in self.graph : continue
				mutex = self.graph[ int( x ) ][ 'mutex' ]
				for m in mutex :
					if not self.nodes[ m ][ 'isaction' ] : continue
					clauses.append( [ "-%s" % x , str( -m ) ] )
		return clauses

	# Convert propositions in CNF File
	def generateCNF( self ) :
		filename = "%s/%s%s%s.cnf" % ( self.directory , self.domain[ 'domain_name' ] , VAR_DELIMITER , self.steps )
		print "Generating %s" % filename
		# Clauses for satisfying goal
		goal = []
		idgoal = self.total * self.steps + len( self.predicates ) + 1
		goal.extend( self.getPreactionClauses( idgoal , True ) )
		# Clauses by levels
		clauses = []
		for lvl in range( self.steps , 0 , -1 ) :
			start = ( lvl - 1 ) * self.total + len( self.predicates ) + 1
			end = start + len( self.actions )
			for actid in range( start , end ) :
				if actid not in self.nodes : continue
				clauses.extend( self.getPreactionClauses( actid ) )
		# Standarized number of variables
		( numvars , impl ) = self.standarize( goal , clauses )
		numclauses = len( impl )
		# Print in CNF file
		f = open( filename , 'w' )
		f.write( "p cnf %s %s\n" % ( numvars , numclauses ) )
		for cl in impl : f.write( "%s 0\n" % ' '.join( cl ) )
		return filename

	# TODO
	def parseSolution( self , cnfsolution ) :
		print cnfsolution
		print self.translator
		idgoal = self.total * self.steps + len( self.predicates ) + 1
		for x in cnfsolution :
			valid = int( x )
			if valid < 0 : continue
			if self.translator[ valid ] == idgoal : continue
			print self.nodes[ self.translator[ valid ] ]
		return []
	
	def debug( self ) :
		print "======== START ========"
		for x in self.start : print x
		print "======== GOAL ========"
		for x in self.goal : print x
		print "======== PREDICATES ========"
		for x in self.predicates : print x
		print "======== ACTIONS ========"
		for x in self.actions : print x
		print "======== VAR ========"
		for x in self.var : print "%s: %s" % ( x , self.var[ x ] )
		self.printgraphrelations()
	
	def printgraphrelations( self ) :
		print "======== GRAPH ========"
		for x in self.nodes :
			node = self.nodes[ x ]
			reprs = '%s%s_%s' % ( '' if node[ 'state' ] else '~' , node[ 'name' ] , node[ 'time' ] )
			childs = ' -> %s' % self.graph[ x ] if x in self.graph else ''
			print '%s: %s%s' % ( x , reprs , childs )

if __name__ == "__main__" :
	if len( sys.argv ) >= 3 :
		if len( sys.argv ) > 3 : DEBUG = sys.argv[ 3 ]
		stripsfile = sys.argv[ 1 ]
		solver = Blackbox( stripsfile )
		situationfile = sys.argv[ 2 ]
		solver.solve( situationfile )
	else :
		print 'Usage: %s [strips_filename] [scenary_filename]' % sys.argv[ 0 ]
