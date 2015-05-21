import os
import re
import time
from utils import *
from subprocess import call
from copy import deepcopy as copy

VAR_DELIMITER = '_'
SATSOLVER = './../satsolver/zchaff'

class Solver :
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
		outfile = open( outname , 'w' )
		ret = call( satsolver , stdout = outfile )
		if ret == 0 : return self.isSatisfiable( outname )
		return len( self.implications ) > 0
	
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
	
	def extractSolution( self ) :
		print "Extracting solution for %s" % self.domain[ 'domain_name' ]
		filename = "%s/%s_%s.out" % ( self.directory , self.domain[ 'domain_name' ] , self.steps )
		with open( filename , 'r' ) as f :
			sol = []
			for line in f :
				if not line.startswith( 'v' ) : continue
				sp = line.split()[ 1: ]
				if '0' in sp : break
				sol.extend( [ self.getProposition( int( w ) ) for w in sp ] )
			idx = 0
			resp = []
			for k in range( self.steps + 1 ) :
				count = 0
				t = {}
				while idx < len( sol ) and count < self.total :
					if sol[ idx ].find( '~' ) < 0 :
						if sol[ idx ] in getAllValues( self.actions , 'name' ) : t[ 'action' ] = sol[ idx ]
						else :
							if 'props' not in t : t[ 'props' ] = []
							t[ 'props' ].append( sol[ idx ] )
					idx += 1
					count += 1
				resp.append( t )
		numvars = len( self.predicates ) + self.total * self.steps
		numclauses = len( self.implications ) + len( self.start ) + len( self.goal )
		return ( resp , numvars , numclauses ) 

	def solve( self , situationfile ) :
		start_time = time.time()
		print "Pre-processing information in %s" % situationfile
		self.preprocess( situationfile )
		self.process()
		( solution , numvars , numclauses ) = self.extractSolution()
		outfile = situationfile.replace( '.in' , '.out' )
		elapsed_time = time.time() - start_time
		self.saveSolution( solution , numvars , numclauses , elapsed_time , outfile )
	
	def extractSolution( self ) :
	 	print "Extracting solution for %s" % self.domain[ 'domain_name' ]
		filename = "%s/%s_%s.out" % ( self.directory , self.domain[ 'domain_name' ] , self.steps )
		numvars = len( self.predicates ) + self.total * self.steps
		numclauses = len( self.implications ) + len( self.start ) + len( self.goal )
		with open( filename , 'r' ) as f :
			sol = []
			for line in f :
				sp = line.split()[ :numvars ]
				if len( sp ) != numvars : continue
				resp = []
				sol.extend( [ self.getProposition( int( w ) ) for w in sp ] )
				idx = 0
				for k in range( self.steps + 1 ) :
					count = 0
					t = {}
					while idx < len( sol ) and count < self.total :
						if sol[ idx ].find( '~' ) < 0 :
							if sol[ idx ] in getAllValues( self.actions , 'name' ) :
								t[ 'action' ] = sol[ idx ]
							else :
								if 'props' not in t : t[ 'props' ] = []
								t[ 'props' ].append( sol[ idx ] )
						idx += 1
						count += 1
					resp.append( t )
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
