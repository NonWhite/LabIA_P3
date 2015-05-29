import os
import re
import time
from converter import *
from utils import *
from subprocess import call
from copy import deepcopy as copy

VAR_DELIMITER = '_'
SATSOLVER = './../satsolver/zchaff'

class Solver :
	def __init__( self , stripsfile ) :
		self.domain = convertToJson( stripsfile )
		self.implications = []
		self.predicates = []
		self.actions = []
		self.var = {}
		self.steps = 0

	def getParameters( self , s ) :
		props = s.replace( '\n' , '' ).split( ';' )
		for i in range( len( props ) ) :
			name = self.searchInDomain( props[ i ] )[ 'name' ]
			lst = props[ i ][ len( name ) + 1 : ].split( '_' )
			lst = [ w for w in lst if len( w ) > 0 ]
			props[ i ] = { 'name' : name , 'parameters' : lst }
		return props

	def getStartAndGoal( self , situationfile ) :
		self.init = self.goal = []
		with open( situationfile , 'r' ) as f :
			lines = f.readlines()
			self.start = self.getParameters( lines[ 0 ] )
			self.goal = self.getParameters( lines[ 1 ] )
	
	def searchInDomain( self , name ) :
		resp = {}
		match = ''
		for pred in self.domain[ 'predicates' ] :
			if name.startswith( pred[ 'name' ] ) :
				if len( pred[ 'name' ] ) > len( match ) :
					match = pred[ 'name' ]
					resp = pred
		return resp

	def addVariable( self , prop , variables , isAction = False , idvar = 0 ) :
		if idvar == len( prop[ 'parameters' ] ) : return [ prop ]
		lst = []
		( varname , typ ) = prop[ 'parameters' ][ idvar ]
		name = prop[ 'name' ]
		for value in variables[ typ ] :
			if value in name.split( VAR_DELIMITER ) : continue
			current = copy( prop )
			current[ 'name' ] += VAR_DELIMITER + value
			if isAction :
				for p in current[ 'precondition' ] :
					if varname not in p[ 'parameters' ] : continue
					p[ 'name' ] = p[ 'name' ].replace( '?' + varname , value )
					p[ 'parameters' ].remove( varname )
				for e in current[ 'effect' ] :
					if varname not in e[ 'parameters' ] : continue
					e[ 'name' ] = e[ 'name' ].replace( '?' + varname , value )
					e[ 'parameters' ].remove( varname )
			lst.extend( self.addVariable( current , variables , isAction , idvar + 1 ) )
		return lst

	def evaluateWith( self , prop , isAction = False , variables = None ) :
		if variables == None : variables = self.var
		if isAction :
			prop[ 'precondition' ] = prop[ 'precondition' ][ 'terms' ]
			prop[ 'effect' ] = prop[ 'effect' ][ 'terms' ]
			for pre in prop[ 'precondition' ] :
				for params in pre[ 'parameters' ] :
					pre[ 'name' ] += VAR_DELIMITER + '?' + params
			for ef in prop[ 'effect' ] :
				for params in ef[ 'parameters' ] :
					ef[ 'name' ] += VAR_DELIMITER + '?' + params
		lst = self.addVariable( prop.copy() , variables , isAction )
		if not isAction :
			for i in range( len( lst ) ) :
				lst[ i ] = lst[ i ][ 'name' ]
		else :
			for act in lst :
				keys = [ 'precondition' , 'effect' ]
				for k in keys :
					for x in act[ k ] : x.pop( 'parameters' , '' )
				act.pop( 'parameters' , '' )
		return lst

	def preprocess( self , situationfile ) :
		'''
		Implement this
		'''
	
	def getID( self , prop ) :
		'''
		Implement this
		'''
	
	def getProposition( self , ID ) :
		'''
		Implement this
		'''

	def generateCNF( self ) :
		'''
		Implement this
		'''

	def getStateFromCNF( self , cnffile ) :
		print "Solving %s" % cnffile
		satsolver = [ SATSOLVER , cnffile ]
		outname = cnffile.replace( '.cnf' , '.out' )
		if not os.path.isfile( outname ) :
			outfile = open( outname , 'w' )
			ret = call( satsolver , stdout = outfile )
		return self.isSatisfiable( outname )
	
	def isSatisfiable( self , filename ) :
		with open( filename , 'r' ) as f :
			for line in f :
				if not line.startswith( 'RESULT' ) : continue
				resp = line.split()[ 1 ]
				return resp == "SAT"
		return False

	def isSolved( self ) :
		cnffile = self.generateCNF()
		return self.getStateFromCNF( cnffile )
	
	def addAction( self ) :
		'''
		Implement this
		'''

	def process( self ) :
		while True :
			self.addAction()
			if self.isSolved() : break
	
	def solve( self , situationfile ) :
		outfile = situationfile.replace( '.in' , '.out' )
		if os.path.isfile( outfile ) : return
		start_time = time.time()
		print "Pre-processing information in %s" % situationfile
		self.initialize( situationfile )
		self.preprocess()
		self.process()
		( solution , numvars , numclauses ) = self.extractSolution()
		elapsed_time = time.time() - start_time
		self.saveSolution( solution , numvars , numclauses , elapsed_time , outfile )
	
	def parseSolution( self , cnfsolution ) :
		'''
		Implement this
		'''
	
	def extractParameters( self , cnffile ) :
		( numvars , numclauses ) = ( 1000 , 1000 )
		with open( cnffile , 'r' ) as f :
			line = ( f.readlines()[ 0 ] ).split()
			( numvars , numclauses ) = ( int( line[ 2 ] ) , int( line[ 3 ] ) )
		return ( numvars , numclauses )

	def extractSolution( self ) :
	 	print "Extracting solution for %s" % self.domain[ 'domain_name' ]
		filename = "%s/%s_%s.out" % ( self.directory , self.domain[ 'domain_name' ] , self.steps )
		cnffile = "%s/%s_%s.cnf" % ( self.directory , self.domain[ 'domain_name' ] , self.steps )
		( numvars , numclauses ) = self.extractParameters( cnffile )
		resp = []
		with open( filename , 'r' ) as f :
			for line in f :
				sp = line.split()[ :numvars ]
				if len( sp ) != numvars : continue
				if not isnumber( sp[ 0 ] ) : continue
				resp = self.parseSolution( sp )
				break
		return ( resp , numvars , numclauses )
	
	def saveSolution( self , sol , numvars , numclauses , elapsed_time , outfile ) :
		if os.path.isfile( outfile ) : return
		with open( outfile , 'w' ) as f :
			f.write( "TIME = %.2f\n" % elapsed_time )
			f.write( "PROPS = %s\n" % numvars )
			f.write( "CLAUSES = %s\n" % numclauses )
			f.write( "SIZE = %s\n" % ( len( sol ) - 1 ) )
			f.write( "SOLUTION\n" )
			for i in range( len( sol ) ) :
				for k in range( len( sol[ i ][ 'props' ] ) ) :
					if k : f.write( ';' )
					f.write( "%s" % sol[ i ][ 'props' ][ k ] )
				f.write( '\n' )
				if 'action' in sol[ i ] :
					f.write( "%s\n" % sol[ i ][ 'action' ] )

	def initialize( self , situationfile ) :
		self.getStartAndGoal( situationfile )
		self.directory = os.path.dirname( situationfile )
		# Get how many variables has for each type (extracted from start and goal)
		stg = []
		for x in self.start : stg.append( x )
		for x in self.goal : stg.append( x )
		for prop in stg :
			name = prop[ 'name' ]
			params = prop[ 'parameters' ]
			obj = self.searchInDomain( name )
			for i in range( len( obj[ 'parameters' ] ) ) :
				typ = obj[ 'parameters' ][ i ][ 1 ]
				if typ not in self.var: self.var[ typ ] = []
				if params[ i ] not in self.var[ typ ] :
					self.var[ typ ].append( params[ i ] )
		# Evaluate predicates with all variables detected
		for pred in self.domain[ 'predicates' ] :
			self.predicates.extend( self.evaluateWith( pred.copy() , isAction = False ) )
		# Evaluate actions with all variables detected
		for act in self.domain[ 'actions' ] :
			self.actions.extend( self.evaluateWith( act.copy() , isAction = True ) )
		# Get full description for start propositions
		for i in range( len( self.start ) ) :
			name = self.start[ i ][ 'name' ]
			for p in self.start[ i ][ 'parameters' ] :
				name += VAR_DELIMITER + p
			self.start[ i ] = { 'name' : name , 'state' : True }
		for pred in self.predicates :
			if pred not in getAllValues( self.start , 'name' ) :
				self.start.append( { 'name' : pred , 'state' : False } )
		for act in self.actions :
			for pre in getAllValues( act[ 'precondition' ] , 'name' ) :
				if pre not in getAllValues( self.start , 'name' ) :
					self.start.append( { 'name' : pre , 'state' : False } )
		# Get full name for goal propositions
		for i in range( len( self.goal ) ) :
			name = self.goal[ i ][ 'name' ]
			for p in self.goal[ i ][ 'parameters' ] :
				name += VAR_DELIMITER + p
			self.goal[ i ] = { 'name' : name , 'state': True }
		# Update list of predicates with not recognized propositions at init
		for p in getAllValues( self.start , 'name' ) :
			if p not in self.predicates : self.predicates.append( p )
		self.idpredicates = 1
		self.idactions = len( self.predicates ) + 1
		self.total = len( self.predicates ) + len( self.actions )
		# Get all predicates that are not affected by every action
		for act in self.actions :
			act[ 'persistence' ] = []
			for pred in self.predicates :
				if pred not in getAllValues( act[ 'effect' ] , 'name' ) :
					act[ 'persistence' ].append( { 'name' : pred , 'state' : True } )
