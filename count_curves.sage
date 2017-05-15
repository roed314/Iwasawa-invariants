def num_curves_with_conductor(N):
	DB=CremonaDatabase()
	Cs=DB.isogeny_classes(N)
	ans=0
	for j in range(len(Cs)):
		ans+=len(Cs[j])
	return ans


def num_curves_with_conductor_at_most(M):
	ans=0
	for N in range(1,M+1):
		ans+=num_curves_with_conductor(N)
	return ans

def num_curves_with_conductor_in_range(M1,M2):
	ans=0
	for N in range(M1,M2+1):
		ans+=num_curves_with_conductor(N)
	return ans
